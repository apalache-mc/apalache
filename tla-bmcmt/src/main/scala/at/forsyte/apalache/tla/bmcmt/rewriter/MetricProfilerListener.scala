package at.forsyte.apalache.tla.bmcmt.rewriter

import java.io.{File, FileWriter, PrintWriter}

import at.forsyte.apalache.tla.bmcmt.smt.SolverContextMetrics
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{TlaEx, UID}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import com.typesafe.scalalogging.LazyLogging

/**
 * This listener registers the SMT metrics that are created when an expression is being translated in SMT.
 * These metrics are collected only for those expressions that have source information, which can be
 * displayed to the user.
 *
 * @param sourceStore the storage of source locations
 * @param changeListener the tracer of expression updates
 */
class MetricProfilerListener(sourceStore: SourceStore, changeListener: ChangeListener, outFile: File)
    extends SymbStateRewriterListener with LazyLogging {
  private var _metricsPerId: Map[UID, SolverContextMetrics] = Map()
  private val sourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)
  private var syncTimestampSecMillis: Long = System.currentTimeMillis()

  /**
   * This method is called by the symbolic state rewriter.
   * @param translatedEx an expression to report
   * @param metricsDelta the SMT metrics that were reported during the translation to SMT
   */
  override def onRewrite(translatedEx: TlaEx, metricsDelta: SolverContextMetrics): Unit = {
    val id = translatedEx.ID
    if (changeListener.isDefinedAt(id) || sourceStore.contains(id)) {
      // this expression can be traced back to the source code
      _metricsPerId.get(id) match {
        case None =>
          _metricsPerId += id -> metricsDelta

        case Some(old: SolverContextMetrics) =>
          _metricsPerId += id -> old.add(metricsDelta)
      }

      val now = System.currentTimeMillis()
      if (now - syncTimestampSecMillis >= MetricProfilerListener.FILE_SYNC_MS) {
        syncTimestampSecMillis = now
        dumpToFile()
      }
    }
  }

  def dumpToFile(): Unit = {
    // filter the entries by the minimal weight and then sort them by the weight, in the descending order
    val sortedEntries = _metricsPerId.iterator
      .filter(_._2.weight >= MetricProfilerListener.MIN_WEIGHT)
      .toList
      .sorted(MetricProfilerListener.EntryOrdering)
    val writer = new PrintWriter(new FileWriter(outFile, false))
    try {
      writer.println("# weight,nCells,nConsts,nSmtExprs,location")
      for (entry <- sortedEntries) {
        writer.println(stringOfEntry(entry))
      }
    } finally {
      writer.close()
    }

    logger.info("%d profile entries to be found in %s".format(sortedEntries.size, outFile))
  }

  private def stringOfEntry(entry: (UID, SolverContextMetrics)): String = {
    val (uid, metrics) = entry
    sourceLocator.sourceOf(uid) match {
      case None =>
        // this should not happen, but produce something meaningful
        "%d,%d,%d,%d,undefinedFor%d".format(metrics.weight, metrics.nCells, metrics.nConsts, metrics.nSmtExprs, uid.id)

      case Some(loc) =>
        "%d,%d,%d,%d,%s".format(metrics.weight, metrics.nCells, metrics.nConsts, metrics.nSmtExprs, loc)
    }
  }

  override def dispose(): Unit = {
    dumpToFile()
  }
}

object MetricProfilerListener {

  /**
   * The minimal weight that is required to print a profile entry
   */
  val MIN_WEIGHT = 0

  /**
   * How often (in milliseconds) an update triggers a sync to file.
   */
  val FILE_SYNC_MS = 60000

  protected object EntryOrdering extends Ordering[(UID, SolverContextMetrics)] {
    override def compare(x: (UID, SolverContextMetrics), y: (UID, SolverContextMetrics)): Int = {
      // use the descending weight order
      y._2.weight.compareTo(x._2.weight)
    }
  }
}
