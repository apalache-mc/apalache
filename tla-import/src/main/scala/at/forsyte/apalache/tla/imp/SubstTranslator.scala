package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaTempOper}
import com.typesafe.scalalogging.LazyLogging
import tla2sany.semantic._

/**
  * Translate a module instance. This class needs extensive testing,
  * as the module instantiation rules are quite sophisticated (Ch. 17).
  *
  * @author konnov
  */
class SubstTranslator(sourceStore: SourceStore, context: Context) extends LazyLogging {

  def translate(substInNode: SubstInNode, body: TlaEx): TlaEx = {
    subExpr(mkRenaming(substInNode), body)
  }

  private def subExpr(renaming: Map[String, TlaEx], ex: TlaEx): TlaEx = {
    def subRec(ex: TlaEx): TlaEx = {
      val newEx =
        ex match {
          case NameEx(name) =>
            renaming.getOrElse(name, NameEx(name))

          case LetInEx(body, defs@_*) =>
            def subDecl(d: TlaOperDecl) = {
              d.copy(body = subRec(d.body))
            }

            LetInEx(subRec(body), defs map subDecl: _*)

          case OperEx(op, args@_*) =>
            if (renaming.nonEmpty
              && Seq(TlaActionOper.enabled, TlaActionOper.composition, TlaTempOper.leadsTo).exists(_.name == op.name)) {
              // TODO: find out how to deal with ENABLED and other tricky operators
              logger.warn("Substitution of %s needs care. The current implementation may fail to work.".format(op.name))
            }
            OperEx(op, args map subRec: _*)

          case d => d
        }

      // copy the source info
      sourceStore.find(ex.ID) match {
        case Some(loc) =>
          sourceStore.add(newEx.ID, loc)

        case None =>
          logger.warn("No source for expr@" + ex.ID)
      }
      // return
      newEx
    }

    subRec(ex)
  }

  private def mkRenaming(substInNode: SubstInNode): Map[String, TlaEx] = {
    // In the substitution INSTANCE ... WITH x <- e, the expression e should be evaluated in the context one level up.
    // Consider the following example:
    //    ------------------- MODULE A ----------------------
    //    ------------------- MODULE B ----------------------
    //    ------------------- MODULE C -------------------
    //    VARIABLE x
    //    magic == x /= 2
    //    ===================================================
    //    VARIABLE y
    //    C1 == INSTANCE C WITH x <- y
    //    ===================================================
    //    VARIABLE z
    //    B1 == INSTANCE B WITH y <- z
    //    ===================================================
    //
    // SANY gives us the operator B1!C1!magic == (x /= 2)[x <- y][y <- z]
    // Note that y should be translated in the context of B1, whereas z should be translated in the root context.
    //
    // See issue #143: https://github.com/informalsystems/apalache/issues/143
    val upperLookupPrefix = context.lookupPrefix.dropRight(1)
    val upperContext = context.setLookupPrefix(upperLookupPrefix)
    val exprTranslator = ExprOrOpArgNodeTranslator(sourceStore, upperContext, OutsideRecursion())

    def eachSubst(s: Subst): (String, TlaEx) = {
      val replacement = exprTranslator.translate(s.getExpr)
      // only constants and variables are allowed in the left-hand side of operator substitutions
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
  def apply(sourceStore: SourceStore, context: Context): SubstTranslator = {
    new SubstTranslator(sourceStore, context)
  }
}
