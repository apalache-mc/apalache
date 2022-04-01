package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx, TlaModule, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, PredResult, PredResultFail, PredResultOk}

/**
 * Test whether the expressions fit into the non-recursive fragment, i.e. no recursive functions or operators are used
 *
 * @author
 *   Jure Kukovec
 */
object NonrecursiveLanguagePred extends LanguagePred {

  // A declaration is OK if it's not recursive and its body is OK
  private def operDeclOk(d: TlaOperDecl): PredResult = {
    val failIfRecursive =
      if (d.isRecursive) {
        val recString = s"RECURSIVE ${d.name}(${d.formalParams.map(_ => "_").mkString(",")})"
        PredResultFail(Seq((d.ID, s"$recString. Apalache does not support recursive operators.")))
      } else PredResultOk()
    failIfRecursive.and(isExprOk(d.body))
  }

  override def isExprOk(ex: TlaEx): PredResult = ex match {
    // Just check that no recursive operator was introduced w/ LET
    case LetInEx(body, defs @ _*) =>
      defs.foldLeft(isExprOk(body)) { case (r, d) =>
        r.and(operDeclOk(d))
      }

    // No other TLA operator besides recFunDef introduces recursion, so just iterate over args, if any.
    // We ignore recFunRef, so we don't get multiple error messages per function
    case OperEx(oper, args @ _*) =>
      val seedRes =
        oper match {
          case TlaFunOper.recFunDef =>
            PredResultFail(Seq((ex.ID, s"Apalache does not support recursive functions.")))
          case _ => PredResultOk()
        }

      args.foldLeft[PredResult](seedRes) { case (r, arg) =>
        r.and(isExprOk(arg))
      }
    case _ => PredResultOk()
  }

  // A module is OK if all its operator declarations are OK
  override def isModuleOk(mod: TlaModule): PredResult =
    mod.operDeclarations.foldLeft[PredResult](PredResultOk()) { case (r, d) =>
      r.and(operDeclOk(d))
    }
}
