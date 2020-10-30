package at.forsyte.apalache.tla.lir.storage

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.src.SourceLocation
import com.typesafe.scalalogging.LazyLogging

/**
  * SourceLocator is used to identify locations in the original .tla specification,
  * from which a given expression, possibly derived from a transformation, originates.
  */
sealed case class SourceLocator(sourceMap : SourceMap,
                                changeListener : ChangeListener) extends LazyLogging {
  def sourceOf( id : UID ) : Option[SourceLocation] =
    sourceMap.get( changeListener.traceBack( id ) )

  def sourceOf( ex : TlaEx ) : Option[SourceLocation] =
    sourceOf( ex.ID )


  /**
    * A debugging method that recursively checks whether all subexpressions of the operator body have source information.
    * When this is not the case, the function prints ids of the topmost problematic expressions.
    * This method may be quite slow, so it should be used in the debugging mode only.
    */
  def checkConsistency(decl: TlaOperDecl): Unit = {
    checkConsistency(decl.body)
  }

  /**
    * A debugging method that recursively checks whether all subexpressions of an expression have source information.
    * When this is not the case, the function prints ids of the topmost problematic expressions.
    * This method may be quite slow, so it should be used in the debugging mode only.
    */
  def checkConsistency(ex: TlaEx): Unit = {
    if (sourceOf(ex).isEmpty) {
      var str = ex.toString
      str = if (str.length > 70) str.substring(0, 69) + "..." else str
      logger.error("No source location for expr@%s: %s".format(ex.ID, str))
    } else {
      ex match {
        case OperEx(_, args @ _*) =>
          args foreach checkConsistency

        case LetInEx(body, decls @ _*) =>
          checkConsistency(body)
          decls.foreach(d => checkConsistency(d.body))

        case _ => // do nothing
      }
    }
  }

}
