package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.LetInOper
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import com.typesafe.scalalogging.LazyLogging
import tla2sany.semantic._

/**
  * Translate a module instance. This class needs extensive testing,
  * as the module instantiation rules are quite sophisticated (Ch. 17).
  *
  * @author konnov
  */
class SubstTranslator(environmentHandler: EnvironmentHandler,
                      sourceStore: SourceStore,
                      context: Context) extends LazyLogging {
  // TODO: get rid of environmentHandler, we do not need it anymore

  def translate(substInNode: SubstInNode, body: TlaEx): TlaEx = {
    subExpr(mkRenaming(substInNode), body)
  }

  private def subExpr(renaming: Map[String, TlaEx], ex: TlaEx): TlaEx = {
    def subRec(ex: TlaEx): TlaEx = ex match {
      case NameEx(name) =>
        renaming.getOrElse(name, NameEx(name))

      case OperEx(op: LetInOper, args@_*) =>
        def subDecl(d: TlaOperDecl) = {
          TlaOperDecl(d.name, d.formalParams, subRec(d.body))
        }

        OperEx(new LetInOper(op.defs map subDecl), args map subRec: _*)

      case OperEx(op, args@_*) =>
        if (renaming.nonEmpty
          && Seq(TlaActionOper.enabled, TlaActionOper.composition, TlaTempOper.leadsTo).exists(_.name == op.name)) {
          // TODO: find out how to deal with ENABLED and other tricky operators
          logger.warn("Substitution of %s needs care. The current implementation may fail to work.".format(op.name))
        }
        OperEx(op, args map subRec: _*)

      case d => d
    }

    subRec(ex)
  }

  private def mkRenaming(substInNode: SubstInNode): Map[String, TlaEx] = {
    val exprTranslator = ExprOrOpArgNodeTranslator(environmentHandler, sourceStore, context, OutsideRecursion())

    def eachSubst(s: Subst): (String, TlaEx) = {
      val replacement = exprTranslator.translate(s.getExpr)
      // TODO: what if a constant happens to be an operator?
      if (s.getOp.getKind != ASTConstants.ConstantDeclKind && s.getOp.getKind != ASTConstants.VariableDeclKind) {
        throw new SanyImporterException("Expected a substituted name %s to be a CONSTANT or a VARIABLE, found kind %d"
          .format(s.getOp.getName, s.getOp.getKind))
      }
      // As all declarations have unique names, it should be sufficient to map the name to the expression.
      // SANY should have checked the syntactic and semantic rules for the substitution.
      s.getOp.getName.toString -> replacement
    }

    Map(substInNode.getSubsts map eachSubst: _*)
  }
}

object SubstTranslator {
  def apply(environmentHandler: EnvironmentHandler, sourceStore: SourceStore, context: Context): SubstTranslator = {
    new SubstTranslator(environmentHandler, sourceStore, context)
  }
}
