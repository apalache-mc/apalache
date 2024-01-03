package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{LanguagePred, PredResult, PredResultFail, PredResultOk}

/**
 * This language predicate ensures that all types in the spec are monotypes, that is, no type contains a type variable.
 *
 * @author
 *   Igor Konnov, Informal Systems, 2022
 */
class MonotypeLanguagePred extends LanguagePred {
  override def isExprOk(expr: TlaEx): PredResult = {
    expr match {
      case OperEx(_, args @ _*) =>
        args.foldLeft[PredResult](checkMono(expr.ID, expr.typeTag.asTlaType1())) { case (r, arg) =>
          r.and(isExprOk(arg))
        }

      case LetInEx(body, decls @ _*) =>
        decls.foldLeft(checkMono(body.ID, body.typeTag.asTlaType1())) { case (r, d) =>
          checkMono(d.ID, d.typeTag.asTlaType1())
            .and(isExprOk(d.body))
            .and(r)
        }

      case _ => checkMono(expr.ID, expr.typeTag.asTlaType1())
    }
  }

  override def isModuleOk(mod: TlaModule): PredResult = {
    mod.operDeclarations.foldLeft[PredResult](PredResultOk()) { case (r, d) =>
      isExprOk(d.body)
        .and(checkMono(d.ID, d.typeTag.asTlaType1()))
        .and(r)
    }
  }

  private def checkMono(sourceUid: UID, tt: TlaType1): PredResult = {
    if (tt.usedNames.isEmpty) {
      PredResultOk()
    } else {
      val msg = s"""|Expected a non-polymorphic type, found: ${tt}
                    |You may need to annotate an empty collection.""".stripMargin
      PredResultFail(Seq((sourceUid, msg)))
    }
  }
}

object MonotypeLanguagePred {
  private val singleton = new MonotypeLanguagePred()

  def apply(): MonotypeLanguagePred = singleton
}
