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
   * When translating g = [f EXCEPT ![x1,...,xn] = a], we need to construct a VMT function representation, which differs
   * from that of `f` at exactly one point.
   *
   * Given a function f: (S1,...,Sn) => S, constructed with the rule f(y1,...,yn) = ef, arguments `x1: S1, ..., xn: Sn`,
   * and an expression `a`, constructs a function definition for g, with the rule:
   * ```
   * g(y1, ... yn) = if y1 = x1 /\ ... /\ yn = xn
   *                 then a
   *                 else ef
   * ```
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
      fnArgTerms: List[Term],
      newCaseTerm: Term,
    )(args: List[(String, Sort)],
      baseCaseTerm: Term): FunDef = {
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

    FunDef(gen.newName(), args, ITE(ifCondition, newCaseTerm, baseCaseTerm))
  }

  // Convenience shorthand
  private def rewrite: TlaEx => Term = rewriter.rewrite

  // Applies a fixed renaming scheme to a term tree (e.g. renames all instances of "a" to "b")
  private def replaceFixedLeaf(replacement: Map[Term, Term])(t: Term): Term = {
    val replace = replaceFixedLeaf(replacement) _
    t match {
      case ITE(ifTerm, thenTerm, elseTerm) => ITE(replace(ifTerm), replace(thenTerm), replace(elseTerm))
      case Apply(term, terms @ _*)         => Apply(replace(term), terms.map(replace): _*)
      case And(terms @ _*)                 => And(terms.map(replace): _*)
      case Or(terms @ _*)                  => Or(terms.map(replace): _*)
      case Equiv(lhs, rhs)                 => Equiv(replace(lhs), replace(rhs))
      case Equal(lhs, rhs)                 => Equal(replace(lhs), replace(rhs))
      case Neg(term)                       => Neg(replace(term))
      case Impl(lhs, rhs)                  => Impl(replace(lhs), replace(rhs))
      case Forall(boundVars, term)         => Forall(boundVars, replace(term))
      case Exists(boundVars, term)         => Exists(boundVars, replace(term))
      case FunDef(name, args, body)        => FunDef(name, args, replace(body))
      case _                               => replacement.getOrElse(t, t)
    }
  }

  // Creates a function application from a list of arguments
  private def mkApp(fnTerm: Term, args: List[(String, Sort)]): Term =
    Apply(fnTerm, args.map { case (name, sort) => mkVariable(name, sort) }: _*)

  // Creates axiomatic function equality. Functions f and g are equal over a domain S1 \X ... \X Sn, iff
  // \A (x1,...,xn) \in S1 \X ... \X Sn: f(x1,...,xn) = g(x1,...xn)
  // domain ... List((x1,S1), ..., (xn,Sn))
  // lhs    ... f(x1,...,xn)
  // rhs    ... g(x1,...,xn)
  private def mkAxiomaticFunEq(domain: List[(String, Sort)], lhs: Term, rhs: Term): Term =
    Forall(domain, Equal(lhs, rhs))

  // Assume isApplicable
  override def apply(ex: TlaEx): Term =
    ex match {
      case OperEx(TlaOper.eq | ApalacheOper.assign, lhs, rhs) =>
        // := is just = in VMT
        val lhsTerm = rewrite(lhs)
        val rhsTerm = rewrite(rhs)

        // Assume sorts are equal, so we just match the left sort.
        // If not, this will get caught by Equal's `require` anyhow.
        lhsTerm.sort match {
          // For functions, do axiomatic equality, i.e.
          // f = g <=> \A x \in DOMAIN f: f[x] = g[x]
          case FunctionSort(_, from @ _*) =>
            (lhsTerm, rhsTerm) match {
              case (FunDef(_, largs, lbody), FunDef(_, rargs, rbody)) =>
                // sanity check
                assert(largs.length == rargs.length)
                // We arbitrarily pick one set of argnames (the left), and rename the other body.
                // We rename all instances of rargs in rbody to same-indexed largs
                val renameMap: Map[Term, Term] = largs
                  .zip(rargs)
                  .map { case ((largName, lsort), (rargName, rsort)) =>
                    mkVariable(rargName, rsort) -> mkVariable(largName, lsort)
                  }
                  .toMap
                val renamedRBody = replaceFixedLeaf(renameMap)(rbody)
                mkAxiomaticFunEq(largs, lbody, renamedRBody)

              case (fv: FunctionVar, FunDef(_, args, body)) =>
                mkAxiomaticFunEq(args, mkApp(fv, args), body)
              case (FunDef(_, args, body), fv: FunctionVar) =>
                mkAxiomaticFunEq(args, mkApp(fv, args), body)
              case (lvar: FunctionVar, rvar: FunctionVar) =>
                // we just invent formal argument names
                val inventedVars = from.toList.map { s =>
                  (gen.newName(), s)
                }
                mkAxiomaticFunEq(inventedVars, mkApp(lvar, inventedVars), mkApp(rvar, inventedVars))

              case _ => Equal(lhsTerm, rhsTerm)
            }

          // Otherwise, do direct equality
          case _ => Equal(lhsTerm, rhsTerm)
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
        FunDef(gen.newName(), argList, rewrite(e))

      case OperEx(TlaFunOper.app, fn, arg) =>
        val fnTerm = rewrite(fn)
        // Arity 2+ functions pack their arguments as a single tuple, which we might need to unpack
        val appArgs = arg match {
          case OperEx(TlaFunOper.tuple, args @ _*) => args.map(rewrite)
          case _                                   => Seq(rewrite(arg))
        }

        // When applying a FunDef, we inline it
        fnTerm match {
          case FunDef(_, args, body) =>
            // sanity check
            assert(args.length == appArgs.length)

            val replacementMap: Map[Term, Term] = args
              .zip(appArgs)
              .map { case ((argName, argSort), concrete) =>
                mkVariable(argName, argSort) -> concrete
              }
              .toMap
            // For a function with a rule f(x1,...,xn) = e
            // we inline f(a1,...,an) to e[x1\a1,...,xn\an]
            replaceFixedLeaf(replacementMap)(body)
          case _ => Apply(fnTerm, appArgs: _*)
        }

      case OperEx(TlaFunOper.except, fn, arg, newVal) =>
        val valTerm = rewrite(newVal)
        // Toplevel, arg is always a TLaFunOper.tuple. Within, it's either a single value, or another
        // tuple, in the case of arity 2+ functions
        val fnArgTerms = arg match {
          // ![a,b,...] case
          case OperEx(TlaFunOper.tuple, OperEx(TlaFunOper.tuple, args @ _*)) =>
            args.toList.map(rewrite)
          // ![a] case
          case OperEx(TlaFunOper.tuple, arg) =>
            List(rewrite(arg))

          case invalidArg =>
            throw new IllegalArgumentException(s"Invalid arg for TlaFunOper.except in EUFRule: ${invalidArg}")
        }

        val exceptTermFn = exceptAsNewFunDef(fnArgTerms, valTerm) _

        // Assume fnArgTerms is nonempty.
        // We have two scenarios: the original function is either defined, or symbolic
        // If it is defined, then we have a rule and arguments, which we can just reuse
        // If it is symbolic, we need to invent new variable names and apply it.
        // If it is ever the case, in the future, that this is slow, we can change this code
        // to use Apply in both cases.
        rewrite(fn) match {
          case FunDef(_, args, oldFnBody) =>
            exceptTermFn(args, oldFnBody)
          case fVar @ FunctionVar(_, FunctionSort(_, from @ _*)) =>
            val fnArgPairs = from.toList.map { sort => (gen.newName(), sort) }
            val appArgs = fnArgPairs.map { case (varName, varSort) =>
              mkVariable(varName, varSort)
            }
            exceptTermFn(fnArgPairs, Apply(fVar, appArgs: _*))
          case _ => throw new RewriterException(s"$fn must be a function term.", fn)
        }

      case OperEx(TlaControlOper.ifThenElse, condEx, thenEx, elseEx) =>
        ITE(rewrite(condEx), rewrite(thenEx), rewrite(elseEx))

      case _ => throw new RewriterException(s"EUFRule not applicable to $ex", ex)
    }
}
