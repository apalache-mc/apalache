package at.forsyte.apalache.tla.lir.src

import at.forsyte.apalache.tla.lir.storage.SourceMap
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.{TlaEx, UID}
import com.google.inject.Singleton

/**
 * <p>Implementation of SourceStore <p>
 *
 * @author
 *   Igor Konnov
 */
@Singleton
trait SourceStore extends TransformationListener {

  /**
   * Label an expression id with a source location. Unless you are sure about using this method, use addRec instead.
   *
   * @param id
   *   a valid expression identifier
   * @param location
   *   a source location
   */
  def add(id: UID, location: SourceLocation): Unit

  /**
   * Label an expression and all of its yet unlabelled subexpressions with a source location (assuming that you are
   * using addRec only). This method does not visit subexpressions that are already labelled with source location. So it
   * may miss deep subexpressions that are hidden under already labelled subexpressions.
   *
   * @param rootEx
   *   an expressio
   * @param location
   *   a source location
   */
  def addRec(rootEx: TlaEx, location: SourceLocation): TlaEx

  def find(id: UID): Option[SourceLocation]

  /**
   * Behaves as find, but also logs a warning when find returns None.
   * @param id
   *   an expression identifier
   * @return
   *   Some(location), when the expression has source information, and None otherwise
   */
  def findOrWarn(id: UID): Option[SourceLocation]

  def contains(id: UID): Boolean

  def makeSourceMap: SourceMap
}
