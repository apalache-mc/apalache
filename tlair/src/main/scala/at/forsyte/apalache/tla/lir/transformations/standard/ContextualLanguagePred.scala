package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, PredResult, PredResultOk}

/**
 * A partial implementation of `LanguagePred`, where operator names are rejected if they appear in a context they are
 * undefined in, and toplevel declarations are checked independently and in conjunction.
 */
abstract class ContextualLanguagePred extends LanguagePred {
  override def isModuleOk(mod: TlaModule): PredResult = {
    mod.operDeclarations.foldLeft[PredResult](PredResultOk()) { case (r, d) =>
      r.and(isExprOk(d.body))
    }
  }

  override def isExprOk(expr: TlaEx): PredResult = {
    isOkInContext(Set(), expr)
  }

  protected def allArgsOk(letDefs: Set[String], args: Iterable[TlaEx]): PredResult =
    args.foldLeft[PredResult](PredResultOk()) { case (r, arg) =>
      r.and(isOkInContext(letDefs, arg))
    }

  // Auxiliary method for checking LET-INs
  protected def eachDefRec(ctx: Set[String], ds: Iterable[TlaOperDecl]): PredResult =
    ds.foldLeft[(PredResult, Set[String])]((PredResultOk(), ctx)) {
      case ((partialRes, partialCtx), TlaOperDecl(name, _, body)) =>
        (
            partialRes.and(isOkInContext(partialCtx, body)),
            partialCtx + name,
        )
    }._1

  protected def isOkInContext(letDefs: Set[String], expr: TlaEx): PredResult
}
