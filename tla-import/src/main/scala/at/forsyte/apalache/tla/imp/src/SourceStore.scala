package at.forsyte.apalache.tla.imp.src

import at.forsyte.apalache.tla.lir.src.{RegionTree, SourceLocation}
import at.forsyte.apalache.tla.lir.storage.SourceMap
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, UID}
import com.google.inject.Singleton

import scala.collection.mutable

/**
  * <p>This class maps expression identifiers to regions of source. It maintains the following invariant:
  * If e2 is a subexpression of e1, then region(e2.id) is inside of region(e1.id). This class assumes that
  * the TLA+ expressions have been assigned identifiers.</p>
  *
  * <p>This is the least wasteful implementation that came to my mind. More importantly, it is designed
  *    in such a way that there are no gaps in the source code information, that is, if we store the source location
  *    of an expression, then we also store the source location of every its subexpression.</p>
  *
  * @author Igor Konnov
  */
@Singleton
class SourceStore extends TransformationListener {
  /**
    * A mapping from a filenames to an index in trees. This map is typically quite small.
    */
  private var filenameToIndex: mutable.Map[String, Int] = mutable.HashMap()
  /**
    * An inverse mapping of filenameToIndex.
    */
  private var indexToFilename: mutable.Map[Int, String] = mutable.HashMap()
  /**
    * A sequence of region trees, one per filename. The following invariant is maintained: filenames.size == trees.size.
    */
  private var trees: Seq[RegionTree] = Seq()

  /**
    * A sequence of mappings from an expression id to a region index, one per filename.
    */
  private var idToRegion: Seq[mutable.Map[UID, Int]] = Seq()

  /**
    * Propagate the source data from the original expression to its replacement
    * @param originEx the original expression
    * @param newEx its replacement
    */
  override def onTransformation(originEx: TlaEx, newEx: TlaEx): Unit = {
    if (originEx.ID != newEx.ID) {
      find(originEx.ID) match {
        case Some(loc) => addRec(newEx, loc)
        case None =>
        // FIXME: throw this exception as soon as we fix the source tracking
        /*
        throw new IllegalArgumentException("The original expression (UID = %s) does not have source data: %s"
          .format(originEx.ID, originEx))
         */
      }
    }
  }

  /**
    * Label an expression id with a source location. Unless you are sure about using this method, use addRec instead.
 *
    * @param id a valid expression identifier
    * @param location a source location
    */
  def add(id: UID, location: SourceLocation): Unit = {
    val (filenameIndex, regionIndex) = addRegion(location)
    idToRegion(filenameIndex).update(id, regionIndex)
  }

  /**
    * Label an expression and all of its yet unlabelled subexpressions with a source location
    * (assuming that you are using addRec only). This method does not visit subexpressions that are already labelled
    * with source location. So it may miss deep subexpressions that are hidden under already labelled subexpressions.
    *
    * @param rootEx an expressio
    * @param location a source location
    */
  def addRec(rootEx: TlaEx, location: SourceLocation): TlaEx = {
    val (filenameIndex, regionIndex) = addRegion(location)
    val map = idToRegion(filenameIndex)
    def add(ex: TlaEx): Unit = {
      val exId = ex.ID
      if (!map.contains(exId)) {
        map += exId -> regionIndex
        ex match {
          case OperEx(_, args @ _*) => args foreach add
          case _ => ()
        }
      } // else: this subexpression has been labelled with the region already, skip
    }
    add(rootEx)
    rootEx
  }

  private def addRegion(loc: SourceLocation): Tuple2[Int, Int] = {
    val filenameIndex = getOrCreateFilenameIndex(loc.filename)
    val regionIndex = trees(filenameIndex).add(loc.region)
    (filenameIndex, regionIndex)
  }

  def find(id: UID): Option[SourceLocation] = {
    idToRegion.zipWithIndex.find(_._1.contains(id)) match {
      case Some((map, filenameIndex)) =>
        // we are using many sequence iterations, but the sequences are quite small
        val regionIndex = map(id)
        val tree = trees(filenameIndex)
        val region = tree.apply(regionIndex)
        Some(SourceLocation(indexToFilename(filenameIndex), region))

      case None => None
    }
  }

  def contains(id: UID): Boolean = {
    find(id).isDefined
  }

  private def getOrCreateFilenameIndex(filename: String): Int = {
    filenameToIndex.get(filename) match {
      case Some(index) =>
        index

      case None =>
        val newIndex = trees.size
        filenameToIndex += (filename -> newIndex)
        indexToFilename += (newIndex -> filename)
        trees :+= new RegionTree()
        idToRegion :+= mutable.HashMap()
        newIndex
    }
  }

  def makeSourceMap: SourceMap = {
    val keys = idToRegion.map( _.keySet).foldLeft( Set.empty[UID] ){ _ ++ _ }
    val pairs = keys map { k =>
      k -> find(k).get
    }
    pairs.toMap
  }
}
