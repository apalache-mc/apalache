package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{And, BoolExpr, True}
import at.forsyte.apalache.tla.lir.formulas.EUF._
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaControlOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

/**
 * EUFRule defines translations for reTLA patterns which encode equality, introduce values defined by if-then else, or
 * define, apply or update functions.
 *
 * @author
 *   Jure Kukovec
 */
class EUFRule(rewriter: Rewriter, restrictedSetJudgement: RestrictedSetJudgement, gen: UniqueNameGenerator)
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
   * Given a function f: (S1,...,Sn) => S, with the rule f(y1,...,yn) = ef, args `x1: S1, ..., xn: Sn`, and an
   * expression eg, constructs a function definition for g, with the rule:
   * ```
   * g(y1, ... yn) = if y1 = x1 /\ ... /\ yn = xn
   *                 then eg
   *                 else ef
   * ```
   * @param fnArgTerms
   *   the values `x1, ..., xn`
   * @param newCaseTerm
   *   the term `eg`
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

  // Assume isApplicable
  override def apply(ex: TlaEx): Term =
    ex match {
      case OperEx(TlaOper.eq | ApalacheOper.assign, lhs, rhs) =>
        // := is just = in VMT
        Equal(rewrite(lhs), rewrite(rhs))

      case OperEx(TlaFunOper.funDef, e, varsAndSets @ _*)
          // All domain-defining sets must be restricted.
          if TlaOper.deinterleave(varsAndSets)._2.forall(isRestrictedSet) =>
        val (vars, sets) = TlaOper.deinterleave(varsAndSets)
        val setSorts = sets.map(restrictedSetJudgement.getSort)
        // Construct pairs of formal parameter names and sorts
        val argList = vars.zip(setSorts).toList.map { case (NameEx(name), sort) =>
          (name, sort)
        }
        FunDef(gen.newName(), argList, rewrite(e))
      case OperEx(TlaFunOper.app, fn, arg) =>
        val fnTerm = rewrite(fn)
        // Arity 2+ functions pack their arguments as a single tuple, which we might need to unpack
        arg match {
          case OperEx(TlaFunOper.tuple, args @ _*) => Apply(fnTerm, args.map(rewrite): _*)
          case _                                   => Apply(fnTerm, rewrite(arg))
        }

      case OperEx(TlaFunOper.except, fn, arg, newVal) =>
        val valTerm = rewrite(newVal)
        // Toplevel, arg is always a TLaFunOper.tuple. within, it's either a single value, or another
        // tuple, in the case of arity 2+ functions
        val fnArgTerms = arg match {
          // ![a,b,...] case
          case OperEx(TlaFunOper.tuple, OperEx(TlaFunOper.tuple, args @ _*)) =>
            args.toList.map(rewrite)
          // ![a] case
          case OperEx(TlaFunOper.tuple, arg) =>
            List(rewrite(arg))
        }

        val exceptTermFn = exceptAsNewFunDef(fnArgTerms, valTerm) _

        // Assume fnArgTerms nonempty
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

      case OperEx(TlaControlOper.ifThenElse, ifEx, thenEx, elseEx) =>
        ITE(rewrite(ifEx), rewrite(thenEx), rewrite(elseEx))

      case _ => throw new RewriterException(s"EUFRule not applicable to $ex", ex)
    }
}
