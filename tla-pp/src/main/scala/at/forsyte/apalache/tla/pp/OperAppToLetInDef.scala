package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaOper}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TlaModuleTransformation, TransformationTracker}
import TypedPredefs._

/**
 * Replaces instances of user-defined operator applications with a LET-IN wrapper.
 *
 * Example:
 * A(x,y) ~~> LET App_1 == A(x,y) IN App_1
 *
 * Operator constants and formal parameters are ignored.
 */
class OperAppToLetInDef(
    nameGenerator: UniqueNameGenerator, tracker: TransformationTracker
) {

  import OperAppToLetInDef.NAME_PREFIX

  private def setTracking(oldEx: => TlaEx, newEx: => TlaEx): TlaEx = {
    val tr = tracker.trackEx { _ =>
      newEx
    }
    tr(oldEx)
  }

  def wrap(wrappableNames: Set[String]): TlaExTransformation = tracker.trackEx {
    case ex @ OperEx(TlaOper.apply, ne @ NameEx(opName), args @ _*)
        if wrappableNames.contains(opName) && args.nonEmpty =>
      val resType = ex.typeTag match {
        case Typed(tt: TlaType1) => tt
        case t                   => throw new TypingException("Expected Typed(_: TlaType1), found: " + t)
      }
      val newArgs = args map wrap(wrappableNames)
      val newEx =
        if (args == newArgs) {
          ex
        } else {
          val app = tla.appOp(ne.copy()(ne.typeTag), newArgs: _*).typed(resType)
          setTracking(ex, app)
        }

      val baseName = IncrementalRenaming.getBase(opName)
      val newName = s"${NAME_PREFIX}_${baseName}_${nameGenerator.newName()}"
      val newDecl = tla
        .declOp(newName, newEx)
        .as(OperT1(Seq(), resType))
      val applyNewDecl = tla.appOp(NameEx(newName)(ne.typeTag)).typed(resType)
      LetInEx(applyNewDecl, newDecl)(ex.typeTag)

    case ex @ OperEx(oper, args @ _*) =>
      val newArgs = args map wrap(wrappableNames)
      if (args == newArgs) {
        ex
      } else {
        OperEx(oper, newArgs: _*)(ex.typeTag)
      }

    case ex @ LetInEx(body, defs @ _*) =>
      // Assumption: let-in defined operators are defined in dependency order
      val (newWrappable, newDefs) = defs.foldLeft((wrappableNames, Seq.empty[TlaOperDecl])) {
        case ((partialSet, partialDecls), decl) =>
          val newDecl = decl.copy(body = wrap(partialSet)(decl.body))
          newDecl.isRecursive = decl.isRecursive
          (partialSet + decl.name, partialDecls :+ newDecl)
      }
      val newBody = wrap(newWrappable)(body)
      if (body == newBody && defs == newDefs) {
        ex
      } else {
        LetInEx(newBody, newDefs: _*)(ex.typeTag)
      }

    case ex => ex
  }

  def moduleTransform(wrappableNames: Set[String]): TlaModuleTransformation = { m =>
    val newDecls = m.declarations map {
      case d @ TlaOperDecl(_, _, body) => d.copy(body = wrap(wrappableNames)(body))
      case d                           => d
    }
    new TlaModule(m.name, newDecls)
  }
}

object OperAppToLetInDef {
  val NAME_PREFIX = "CALL"

  def apply(
      nameGenerator: UniqueNameGenerator, tracker: TransformationTracker
  ) = new OperAppToLetInDef(nameGenerator, tracker)
}
