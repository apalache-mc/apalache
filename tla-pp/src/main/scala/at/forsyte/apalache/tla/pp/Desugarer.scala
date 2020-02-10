package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaFunOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.standard.FlatLanguagePred
import at.forsyte.apalache.tla.lir.transformations.{LanguageWatchdog, TlaExTransformation, TransformationTracker}
import javax.inject.Singleton

/**
  * <p>Remove all annoying syntactic sugar. In the future we should move most of the pre-processing code to this class,
  * unless it really changes the expressive power.</p>
  *
  * <p>This transformation assumes that all operator definitions and internal
  * let-definitions have been inlined.</p>
  *
  * <p>TODO: can we make transformation tracking more precise?</p>
  *
  * @author Igor Konnov
  */
@Singleton
class Desugarer(tracker: TransformationTracker) extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    LanguageWatchdog(FlatLanguagePred()).check(expr)
    transform(expr)
  }

  def transform: TlaExTransformation = tracker.track {
      case ex @ NameEx(_) => ex
      case ex @ ValEx(_) => ex
      case ex @ NullEx => ex

      case ex @ OperEx(TlaFunOper.except, fun, args @ _*) =>
        val accessors = args.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val newValues = args.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val nonSingletons = accessors.collect { case OperEx(TlaFunOper.tuple, lst @ _*) => lst.size > 1 }
        if (nonSingletons.isEmpty) {
          // only singleton tuples, do nothing
          ex
        } else {
          // multiple accesses, e.g., ![i][j] = ...
          expandExcept(fun, accessors, newValues)
        }

      case OperEx(TlaActionOper.unchanged, args @ _*) =>
        // flatten all tuples, e.g., convert <<x, <<y, z>> >> to [x, y, z]
        val flatArgs = flattenTuples(tla.tuple(args :_*))
        // and map every x to x' = x
        val eqs = flatArgs map { x => tla.eql(tla.prime(x), x) }
        tla.and(eqs :_*)

      case fex @ OperEx(TlaSetOper.filter, boundEx, setEx, predEx) =>
        OperEx(TlaSetOper.filter, collapseTuplesInFilter(boundEx, setEx, predEx) :_*)

      case fex @ OperEx(TlaSetOper.map, args @ _*) =>
        OperEx(TlaSetOper.map, collapseTuplesInMap(args.head, args.tail) :_*)

      case fex @ OperEx(TlaFunOper.funDef, args @ _*) =>
        OperEx(TlaFunOper.funDef, collapseTuplesInMap(args.head, args.tail) :_*)

      case OperEx(op, args @ _*) =>
        OperEx(op, args map transform :_*)

      case LetInEx( body, defs@_* ) =>
        LetInEx( transform( body ), defs map { d => d.copy( body = transform( d.body ) ) } : _* )
  }

  private def flattenTuples(ex: TlaEx): Seq[TlaEx] = ex match {
    case OperEx(TlaFunOper.tuple, args @ _*) =>
      args.map(flattenTuples).reduce(_ ++ _)

    case NameEx(_) =>
      Seq(ex)

    case _ =>
      throw new IllegalArgumentException("Expected a variable or a tuple of variables, found: " + ex)
  }

  private def expandExcept(topFun: TlaEx, accessors: Seq[TlaEx], newValues: Seq[TlaEx]): TlaEx = {
    def untuple: PartialFunction[TlaEx, Seq[TlaEx]] = { case OperEx(TlaFunOper.tuple, args @ _*) => args }
    def unfoldKey(indicesInPrefix: Seq[TlaEx], indicesInSuffix: Seq[TlaEx], newValue: TlaEx): TlaEx = {
      // produce [f[i_1]...[i_m] EXCEPT ![i_m+1] = unfoldKey(...) ]
      indicesInSuffix match {
        case Nil => newValue // nothing to unfold, just return g
        case oneMoreIndex +: otherIndices =>
          // f[i_1]...[i_m]
          val funApp = indicesInPrefix.foldLeft(topFun) ((f, i) => tla.appFun(f, i))
          // the recursive call defines another chain of EXCEPTS
          val rhs = unfoldKey(indicesInPrefix :+ oneMoreIndex, otherIndices, newValue)
          OperEx(TlaFunOper.except, funApp, tla.tuple(oneMoreIndex), rhs)
      }
    }

    def eachPair(accessor: TlaEx, newValue: TlaEx): (TlaEx, TlaEx) = {
      val indices = untuple(accessor)
      // ![e_1][e_2]...[e_k] = g becomes ![e_1] = h
      val lhs = tla.tuple(indices.head)
      // h is computed by unfoldKey
      val rhs = unfoldKey(Seq(indices.head), indices.tail, newValue)
      (lhs, rhs)
    }
    val expandedPairs = accessors.zip(newValues) map (eachPair _).tupled
    val expandedArgs = 0.until(2 * expandedPairs.size) map
      (i => if (i % 2 == 0) expandedPairs(i / 2)._1 else expandedPairs(i / 2)._2)
    OperEx(TlaFunOper.except, topFun +: expandedArgs :_*)
  }

  /**
    * Transform filter expressions like {<< x, y >> \in S: x = 1} to { x_y \in S: x_y[1] = 1 }
    * @param boundEx a bound expression, e.g., x or << x, y >>
    * @param setEx a set expression, e.g., S
    * @param predEx a predicate expression, e.g., x == 1
    * @return transformed arguments
    */
  def collapseTuplesInFilter(boundEx: TlaEx, setEx: TlaEx, predEx: TlaEx): Seq[TlaEx] = {
    val boundName = mkTupleName(boundEx) // rename a tuple into a name, if needed
    // variable substitutions for the variables inside the tuples
    val subs = collectSubstitutions(Map(), boundEx)
    val newPred = substituteNames(subs, predEx)
    Seq(NameEx(boundName), setEx, newPred)
  }

  /**
    * Transform filter expressions like {x : << x, y >> \in S} to { x_y[1] : x_y \in S }
    * @param mapEx the mapping, e.g., x
    * @param args bindings and sets
    * @return transformed arguments
    */
  def collapseTuplesInMap(mapEx: TlaEx, args: Seq[TlaEx]): Seq[TlaEx] = {
    val boundEs = args.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
    val setEs = args.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
    val boundNames = boundEs map mkTupleName // rename tuples into a names, if needed
    // variable substitutions for the variables inside the tuples
    val subs = boundEs.foldLeft(Map[String, TlaEx]())(collectSubstitutions)
    val newMapEx = substituteNames(subs, mapEx)
    // collect the arguments back
    val newArgs = 0.until(2 * boundEs.length) map
      { i => if (i % 2 == 0) NameEx(boundNames(i / 2)) else setEs(i / 2) }

    newMapEx +: newArgs
  }

  private def collectSubstitutions(subs: Map[String, TlaEx], ex: TlaEx): Map[String, TlaEx] = {
    ex match {
      case NameEx(_) => subs // nothing to do

      case OperEx(TlaFunOper.tuple, _*) =>
        val tupleName = mkTupleName(ex) // introduce a name, e.g., x_y_z for <<x, <<y, z>> >>
        val indices = assignIndicesInTuple(Map(), ex, Seq())
        def indexToTlaEx(index: Seq[Int]): TlaEx = {
          index.foldLeft(tla.name(tupleName): TlaEx) { (e, i) => tla.appFun(e, tla.int(i)) }
        }

        // map every variable inside the tuple to a tuple access, e.g., x -> x_y_z[1] and z -> x_y_z[1][2]
        indices.foldLeft(subs) { (m, p) => m + (p._1 -> indexToTlaEx(p._2))}

      case _ =>
        throw new IllegalArgumentException("Unexpected %s among set filter parameters".format(ex))
    }
  }

  private def mkTupleName(ex: TlaEx): String = {
    ex match {
      case NameEx(name) => name

      case OperEx(TlaFunOper.tuple, args @ _*) =>
        // L and J indicate the beginning and the end of the tuple
        (args map mkTupleName) mkString "_"

      case _ =>
        throw new IllegalArgumentException("Unexpected %s among set filter parameters".format(ex))    }
  }

  private def assignIndicesInTuple(map: Map[String, Seq[Int]], ex: TlaEx, myIndex: Seq[Int]): Map[String, Seq[Int]] = {
    ex match {
      case NameEx(name) =>
        map + (name -> myIndex)

      case OperEx(TlaFunOper.tuple, args @ _*) =>
        def assignRec(m: Map[String, Seq[Int]], p: (TlaEx, Int)) =
          assignIndicesInTuple(m, p._1, myIndex :+ (1 + p._2)) // tuple indices start with 1

        args.zipWithIndex.foldLeft(map)(assignRec)

      case _ =>
        throw new IllegalArgumentException("Unexpected %s among set filter parameters".format(ex))
    }
  }

  private def substituteNames(subs: Map[String, TlaEx], ex: TlaEx): TlaEx = {
    def rename(e: TlaEx): TlaEx = e match {
      case NameEx(name) => if (!subs.contains(name)) e else subs(name)

      case LetInEx( body, defs@_* ) =>
        val newDefs = defs.map( d => d.copy( body = rename( d.body ) ) )
        LetInEx( rename( body ), newDefs : _* )

      case OperEx(op, args @ _*) =>
        OperEx(op, args map rename :_*)

      case _ => e
    }

    rename(ex)
  }
}

object Desugarer {
  def apply(tracker: TransformationTracker): Desugarer = new Desugarer(tracker)
}
