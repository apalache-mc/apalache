package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans.{And, BoolExpr, False, True}
import at.forsyte.apalache.tla.lir.formulas.EUF.{Apply, Equal, FunDef, FunctionVar, ITE}
import at.forsyte.apalache.tla.lir.formulas.StandardSorts.{BoolSort, FunctionSort}
import at.forsyte.apalache.tla.lir.formulas.{FnTerm, Sort, Term}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaControlOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

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

  private def isRestrictedSet(ex: TlaEx) = restrictedSetJudgement.isRestrictedSet(ex)

  private def castToFun(ex: TlaEx): FnTerm = {
    def castEval: Sort => Boolean = {
      case _: FunctionSort => true
      case _               => false
    }
    TermAndSortCaster.rewriteAndCast[FnTerm](rewriter, castEval)(ex)
  }

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
  private def exceptAsNewFunDef(fnArgTerms: List[Term], newCaseTerm: Term)(args: List[(String, Sort)],
      baseCaseTerm: Term): FunDef = {
    // sanity check
    assert(args.length == fnArgTerms.length)

    val matchConds = args.zip(fnArgTerms) map { case ((name, sort), term) =>
      Equal(mkVariable(name, sort), term)
    }

    val ifCondition = matchConds match {
      case Nil      => True // Should never happen
      case h :: Nil => h
      case _        => And(matchConds: _*)
    }

    FunDef(gen.newName(), args, ITE(ifCondition, newCaseTerm, baseCaseTerm))
  }

  // Assume isApplicable
  override def apply(ex: TlaEx): Term =
    ex match {
      case OperEx(TlaOper.eq | ApalacheOper.assign, lhs, rhs) =>
        // := is just = in VMT
        Equal(rewriter.rewrite(lhs), rewriter.rewrite(rhs))
      case OperEx(TlaOper.apply, fn, args @ _*) =>
        throw new RewriterException(s"Not implemented yet", ex)
      case OperEx(TlaControlOper.ifThenElse, ifEx, thenEx, elseEx) =>
        val castIfEx = TermAndSortCaster.rewriteAndCast[BoolExpr](rewriter, BoolSort())(ifEx)
        ITE(castIfEx, rewriter.rewrite(thenEx), rewriter.rewrite(elseEx))

      case OperEx(TlaFunOper.funDef, e, varsAndSets @ _*)
          if TlaOper.deinterleave(varsAndSets)._2 forall isRestrictedSet =>
        val (vars, sets) = TlaOper.deinterleave(varsAndSets)
        val setSorts = sets map restrictedSetJudgement.getSort
        val argList = vars.zip(setSorts).toList map { case (NameEx(name), sort) =>
          (name, sort)
        }
        FunDef(gen.newName(), argList, rewriter.rewrite(e))
      case OperEx(TlaFunOper.app, fn, arg) =>
        val castFn = castToFun(fn)
        Apply(castFn, rewriter.rewrite(arg))

      case OperEx(TlaFunOper.except, fn, arg, newVal) =>
        val valTerm = rewriter.rewrite(newVal)
        val fnArgTerms = arg match {
          // ![a,b,...] case
          case OperEx(TlaFunOper.tuple, OperEx(TlaFunOper.tuple, args @ _*)) =>
            args.toList map rewriter.rewrite
          // ![a] case
          case OperEx(TlaFunOper.tuple, arg) =>
            List(rewriter.rewrite(arg))
        }

        val exceptTermFn = exceptAsNewFunDef(fnArgTerms, valTerm) _

        // Assume fnArgTerms nonempty
        castToFun(fn) match {
          case FunDef(_, args, oldFnBody) =>
            exceptTermFn(args, oldFnBody)
          case fVar @ FunctionVar(_, FunctionSort(_, from @ _*)) =>
            val fnArgPairs = from.toList map { sort => (gen.newName(), sort) }
            val appArgs = fnArgPairs map { case (varName, varSort) =>
              mkVariable(varName, varSort)
            }
            exceptTermFn(fnArgPairs, Apply(fVar, appArgs: _*))
        }
      case _ => throw new RewriterException(s"EUFRule not applicable to $ex", ex)
    }
}
