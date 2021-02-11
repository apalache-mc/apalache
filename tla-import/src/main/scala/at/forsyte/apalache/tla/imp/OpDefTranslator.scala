package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.{SaveToStoreTracker, SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.io.annotations.store._
import tla2sany.semantic.{OpApplNode, OpDefNode}

/**
 * Translate an operator definition to a TlaOper.
 *
 * @author konnov
 */
class OpDefTranslator(
    sourceStore: SourceStore, annotationStore: AnnotationStore, context: Context
) {
  private val annotationExtractor: AnnotationExtractor =
    new AnnotationExtractor(annotationStore)

  def translate(node: OpDefNode): TlaOperDecl = {
    val params = node.getParams.toList map FormalParamTranslator().translate
    val nodeName = node.getName.toString.intern()
    val isRecursive = node.getInRecursive

    if (!isRecursive) {
      node.getBody match {
        case app: OpApplNode if "$RecursiveFcnSpec" == app.getOperator.getName.toString =>
          // this is a definition of a recursive function, translate to recFunDef
          val body =
            ExprOrOpArgNodeTranslator(
                sourceStore,
                annotationStore,
                context,
                OutsideRecursion()
            ).translate(node.getBody)
          val recFunRef = OperEx(TlaFunOper.recFunRef)
          // save the source location of the call to the recursive function, point to the definition
          sourceStore.addRec(
              recFunRef,
              SourceLocation(node.getBody.getLocation)
          )
          // the body still can refer to the function by its name, replace it with recFunRef
          val replaced = ReplaceFixed(
              NameEx(nodeName),
              recFunRef,
              new SaveToStoreTracker(sourceStore)
          )(body)
          // store the source location
          sourceStore.addRec(replaced, SourceLocation(node.getBody.getLocation))
          // return the operator whose body is a recursive function
          val operDecl = TlaOperDecl(nodeName, List(), replaced)
          operDecl.isRecursive = false
          sourceStore.add(operDecl.ID, SourceLocation(node.getLocation))
          annotationExtractor.parseAndSave(operDecl.ID, node)
          operDecl

        case _ =>
          // non-recursive declarations are easy
          val decl = TlaOperDecl(
              nodeName,
              params,
              ExprOrOpArgNodeTranslator(
                  sourceStore,
                  annotationStore,
                  context,
                  OutsideRecursion()
              ).translate(node.getBody)
          )
          sourceStore.add(decl.ID, SourceLocation(node.getLocation))
          annotationExtractor.parseAndSave(decl.ID, node)
          decl
      }
    } else {
      // in recursive declarations, the applications of recursive operators are replaced by calls to formal parameters
      val body =
        ExprOrOpArgNodeTranslator(
            sourceStore,
            annotationStore,
            context,
            InsideRecursion()
        ).translate(node.getBody)
      val decl = TlaOperDecl(nodeName, params, body)
      decl.isRecursive = true
      sourceStore.add(decl.ID, SourceLocation(node.getLocation))
      annotationExtractor.parseAndSave(decl.ID, node)
      decl
    }
  }
}

object OpDefTranslator {
  def apply(
      sourceStore: SourceStore, annotationStore: AnnotationStore, context: Context
  ): OpDefTranslator = {
    new OpDefTranslator(sourceStore, annotationStore, context)
  }
}
