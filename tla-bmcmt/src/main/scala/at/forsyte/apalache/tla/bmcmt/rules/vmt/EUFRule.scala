package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaControlOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

/**
 * EUFRule defines translations for reTLA patterns which encode equality, introduce values defined by if-then else, or
 * define, apply or update functions.
 *
 * @author
 *   Jure Kukovec
 */
class EUFRule(rewriter: ToTermRewriter, restrictedSetJudgement: RestrictedSetJudgement, gen: UniqueNameGenerator)
    extends FormulaRule {

  private val eufOper: Set[TlaOper] = Set(
      TlaOper.eq,
      TlaOper.apply,
      TlaControlOper.ifThenElse,
      ApalacheOper.assign,
      TlaFunOper.funDef,
      TlaFunOper.app,
      TlaFunOper.except,
  )

  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(oper, _*) => eufOper.contains(oper)
      case _                => false
    }

  // Only restricted sets are allowed as function domains
  private def isRestrictedSet(ex: TlaEx) = restrictedSetJudgement.isRestrictedSet(ex)

  /**
   * When translating g = [f EXCEPT ![x1,...,xn] = a], we need to construct a function representation, which differs
   * from that of `f` at exactly one point.
   *
   * Given a function f: (S1,...,Sn) => S, constructed with the rule f(y1,...,yn) = ef, arguments `x1: S1, ..., xn: Sn`,
   * and an expression `a`, constructs a function definition for g, with the rule:
   * {{{
   * g(y1, ... yn) = if y1 = x1 /\ ... /\ yn = xn
   *                 then a
   *                 else ef
   * }}}
   * @param fnArgTerms
   *   the values `x1, ..., xn`
   * @param newCaseTerm
   *   the term `a`
   * @param args
   *   pairs `(y1, S1),...,(yn,Sn)`
   * @param baseCaseTerm
   *   the term `ef`
   * @return
   */
  private def exceptAsNewFunDef(
      fnArgTerms: Seq[Term],
      newCaseTerm: Term,
      args: Seq[(String, Sort)],
      baseCaseTerm: Term): TermBuilderT = {
    // sanity check
    assert(args.length == fnArgTerms.length)

    // Except redefines at a point <<x1, ..., xn>>. We decompose <<y1,...,yn>> = <<x,...xn>>
    // into y1 = x1 /\ ... /\ yn = xn
    val matchConds = args.zip(fnArgTerms).map { case ((name, sort), term) =>
      Equal(mkVariable(name, sort), term)
    }

    // We could use a generic And-wrapper, but it's more convenient to handle nullary and unary cases separately
    val ifCondition = matchConds match {
      case Nil      => True // Should never happen, included for case-completeness
      case h :: Nil => h
      case _        => And(matchConds: _*)
    }

    // We store the new definition, but return a Term (computation)
    defineAndUse(gen.newName(), args, ITE(ifCondition, newCaseTerm, baseCaseTerm))
  }

  // Convenience shorthand
  private def rewrite: TlaEx => TermBuilderT = rewriter.rewrite

  // Creates a function application from a list of arguments
  private def mkApp(fnTerm: Term, args: List[(String, Sort)]): Term =
    Apply(fnTerm, args.map { case (name, sort) => mkVariable(name, sort) }: _*)

  // Assume isApplicable
  override def apply(ex: TlaEx): TermBuilderT =
    ex match {
      case OperEx(TlaOper.eq | ApalacheOper.assign, lhs, rhs) =>
        // := is just = in SMT
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield {
          require(lhsTerm.sort == rhsTerm.sort, "Equality requires terms of equal Sorts.")
          // Assume sorts are equal, so we just match the left sort.
          lhsTerm.sort match {
            // For functions, do axiomatic equality, i.e.
            // f = g <=> \A x \in DOMAIN f: f[x] = g[x]
            case FunctionSort(_, from @ _*) =>
              // we just invent formal argument names
              val inventedVars = from.toList.map { s =>
                (gen.newName(), s)
              }
              // Creates axiomatic function equality. Functions f and g are equal over a domain S1 \X ... \X Sn, iff
              // \A (x1,...,xn) \in S1 \X ... \X Sn: f(x1,...,xn) = g(x1,...xn)
              // domain ... Seq((x1,S1), ..., (xn,Sn))
              // lhs    ... f(x1,...,xn)
              // rhs    ... g(x1,...,xn)
              Forall(inventedVars, Equal(mkApp(lhsTerm, inventedVars), mkApp(rhsTerm, inventedVars)))
            // Otherwise, do direct equality
            case _ => Equal(lhsTerm, rhsTerm)
          }
        }

      case OperEx(TlaFunOper.funDef, e, varsAndSets @ _*)
          // All domain-defining sets must be restricted.
          if TlaOper.deinterleave(varsAndSets)._2.forall(isRestrictedSet) =>
        val (vars, sets) = TlaOper.deinterleave(varsAndSets)
        val setSorts = sets.map(restrictedSetJudgement.getSort)
        // Construct pairs of formal parameter names and sorts
        val argList = vars.zip(setSorts).toList.map {
          case (NameEx(name), sort) => (name, sort)
          case (ex, _)              => throw new RewriterException(s"$ex must be a name.", ex)
        }
        for {
          rewrittenE <- rewrite(e)
          funTerm <- defineAndUse(gen.newName(), argList, rewrittenE)
        } yield funTerm

      case OperEx(TlaFunOper.app, fn, arg) =>
        val fnTermCmp = rewrite(fn)
        // Arity 2+ functions pack their arguments as a single tuple, which we might need to unpack
        val appArgsCmp = arg match {
          case OperEx(TlaFunOper.tuple, args @ _*) => args.map(rewrite)
          case _                                   => Seq(rewrite(arg))
        }

        for {
          fnTerm <- fnTermCmp
          args <- cmpSeq(appArgsCmp)
        } yield Apply(fnTerm, args: _*)

      case OperEx(TlaFunOper.except, fn, arg, newVal) =>
        val valTermCmp = rewrite(newVal)
        // Toplevel, arg is always a TLaFunOper.tuple. Within, it's either a single value, or another
        // tuple, in the case of arity 2+ functions
        val fnArgTermsCmp = arg match {
          // ![a,b,...] case
          case OperEx(TlaFunOper.tuple, OperEx(TlaFunOper.tuple, args @ _*)) =>
            args.map(rewrite)
          // ![a] case
          case OperEx(TlaFunOper.tuple, arg) =>
            Seq(rewrite(arg))

          case invalidArg =>
            throw new IllegalArgumentException(s"Invalid arg for TlaFunOper.except in EUFRule: ${invalidArg}")
        }

        for {
          valTerm <- valTermCmp
          fnArgTerms <- cmpSeq(fnArgTermsCmp)
          fnTerm <- rewrite(fn)
          newFnTerm <-
            // Assume fnArgTerms is nonempty.
            // We need to invent new variable names and apply the function.
            fnTerm match {
              case fVar @ FunctionVar(_, FunctionSort(_, from @ _*)) =>
                val fnArgPairs = from.toList.map { sort => (gen.newName(), sort) }
                val appArgs = fnArgPairs.map { case (varName, varSort) =>
                  mkVariable(varName, varSort)
                }
                exceptAsNewFunDef(fnArgTerms, valTerm, fnArgPairs, Apply(fVar, appArgs: _*))
              case _ => throw new RewriterException(s"$fn must be a function term.", fn)
            }
        } yield newFnTerm

      case OperEx(TlaControlOper.ifThenElse, condEx, thenEx, elseEx) =>
        for {
          condTerm <- rewrite(condEx)
          thenTerm <- rewrite(thenEx)
          elseTerm <- rewrite(elseEx)
        } yield ITE(condTerm, thenTerm, elseTerm)

      case _ => throw new RewriterException(s"EUFRule not applicable to $ex", ex)
    }
}
