package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.UntypedPredefs._

import javax.inject.Singleton

/**
 * <p>Remove all annoying syntactic sugar.</p>
 *
 * @author Igor Konnov
 */
@Singleton
class Desugarer(gen: UniqueNameGenerator, tracker: TransformationTracker) extends TlaExTransformation {

  override def apply(expr: TlaEx): TlaEx = {
    transform(expr)
  }

  def transform: TlaExTransformation = tracker.trackEx {
    case ex @ NameEx(_) => ex
    case ex @ ValEx(_)  => ex
    case ex @ NullEx    => ex

    case ex @ OperEx(TlaFunOper.except, fun, args @ _*) =>
      val trArgs = args map transform
      val (accessors, newValues) = TlaOper.deinterleave(trArgs)
      val isMultidimensional = accessors.exists { case OperEx(TlaFunOper.tuple, lst @ _*) => lst.size > 1 }
      if (accessors.length < 2 && !isMultidimensional) {
        // the simplest update [ f EXCEPT ![i] = e ]
        OperEx(TlaFunOper.except, transform(fun) +: trArgs: _*)(ex.typeTag)
      } else {
        // we have one of the following (or both):
        //   1. a multi-dimension index: [f ![i_1]...[i_m] = e]
        //   2. multiple indices: [f !a_1 = e_1, ..., !a_n = e_n]
        expandExcept(transform(fun), accessors, newValues)
      }

    case OperEx(TlaActionOper.unchanged, args @ _*) =>
      // flatten all tuples, e.g., convert <<x, <<y, z>> >> to [x, y, z]
      // construct a tuple for flattenTuplesInUnchanged, the type is bogus, as the tuple will be unpacked
      val asTuple = tla.tuple(args.map(transform(_)): _*).untyped()
      val flatArgs = flattenTuplesInUnchanged(asTuple)
      // map every x to x' = x
      val eqs = flatArgs map { x => tla.eql(tla.prime(x), x) }
      // x' = x /\ y' = y /\ z' = z
      eqs match {
        case Seq() =>
          // results from UNCHANGED <<>>, UNCHANGED << << >> >>, etc.
          tla.bool(true).untyped()

        case Seq(one) =>
          one.untyped()

        case _ =>
          tla.and(eqs: _*).untyped()
      }

    case OperEx(TlaOper.eq, OperEx(TlaFunOper.tuple, largs @ _*), OperEx(TlaFunOper.tuple, rargs @ _*)) =>
      // <<e_1, ..., e_k>> = <<f_1, ..., f_n>>
      // produce pairwise comparison
      if (largs.length != rargs.length) {
        tla.bool(false).untyped()
      } else {
        val eqs = largs.zip(rargs) map { case (l, r) => tla.eql(this(l), this(r)) }
        tla.and(eqs: _*).untyped()
      }

    case OperEx(TlaOper.ne, OperEx(TlaFunOper.tuple, largs @ _*), OperEx(TlaFunOper.tuple, rargs @ _*)) =>
      // <<e_1, ..., e_k>> /= <<f_1, ..., f_n>>
      // produce pairwise comparison
      if (largs.length != rargs.length) {
        tla.bool(true).untyped()
      } else {
        val neqs = largs.zip(rargs) map { case (l, r) => tla.neql(this(l), this(r)) }
        tla.or(neqs: _*).untyped()
      }

    case ex @ OperEx(TlaSetOper.filter, boundEx, setEx, predEx) =>
      // rewrite { <<x, <<y, z>> >> \in XYZ: P(x, y, z) }
      // to { x_y_z \in XYZ: P(x_y_z[1], x_y_z[1][1], x_y_z[1][2]) }
      OperEx(TlaSetOper.filter, collapseTuplesInFilter(transform(boundEx), transform(setEx), transform(predEx)): _*)(
          ex.typeTag)

    case ex @ OperEx(TlaBoolOper.exists, boundEx, setEx, predEx) =>
      // rewrite \E <<x, <<y, z>> >> \in XYZ: P(x, y, z)
      // to \E x_y_z \in XYZ: P(x_y_z[1], x_y_z[1][1], x_y_z[1][2])
      OperEx(TlaBoolOper.exists, collapseTuplesInFilter(transform(boundEx), transform(setEx), transform(predEx)): _*)(
          ex.typeTag)

    case ex @ OperEx(TlaBoolOper.forall, boundEx, setEx, predEx) =>
      // rewrite \A <<x, <<y, z>> >> \in XYZ: P(x, y, z)
      // to \A x_y_z \in XYZ: P(x_y_z[1], x_y_z[1][1], x_y_z[1][2])
      OperEx(TlaBoolOper.forall, collapseTuplesInFilter(transform(boundEx), transform(setEx), transform(predEx)): _*)(
          ex.typeTag)

    case ex @ OperEx(TlaSetOper.map, args @ _*) =>
      // rewrite { <<x, <<y, z>> >> \in XYZ |-> e(x, y, z) }
      // to { x_y_z \in XYZ |-> e(x_y_z[1], x_y_z[1][1], x_y_z[1][2])
      val trArgs = args map transform
      OperEx(TlaSetOper.map, collapseTuplesInMap(trArgs.head, trArgs.tail): _*)(ex.typeTag)

    case ex @ OperEx(funDefOp, args @ _*) if (funDefOp == TlaFunOper.funDef || funDefOp == TlaFunOper.recFunDef) =>
      val trArgs = args map transform
      val fun = trArgs.head
      val (vars, sets) = TlaOper.deinterleave(trArgs.tail)
      val (onlyVar, onlySet) =
        if (vars.length > 1) {
          // a function of multiple arguments: Introduce a tuple to contain all these arguments
          // we will need types in the future, commented out for now
          //  val pointType = TupT1(vars.map(_.typeTag.asTlaType1()): _*)
          val point = tla.tuple(vars: _*).untyped() // future: typed(pointType)
          val plane = tla.times(sets: _*).untyped() // future: typed(SetT1(pointType))
          // track the modification to point to the first variable and set
          tracker.hold(vars.head, point)
          tracker.hold(sets.head, plane)
          (point, plane)
        } else {
          (vars.head, sets.head)
        }
      // transform the function into a single-argument function and collapse tuples
      OperEx(funDefOp, collapseTuplesInMap(fun, Seq(onlyVar, onlySet)): _*)(ex.typeTag)

    case ex @ OperEx(op, args @ _*) =>
      OperEx(op, args map transform: _*)(ex.typeTag)

    case ex @ LetInEx(body, defs @ _*) =>
      LetInEx(transform(body), defs map { d => d.copy(body = transform(d.body)) }: _*)(ex.typeTag)
  }

  private def flattenTuplesInUnchanged(ex: TlaEx): Seq[TlaEx] = ex match {
    case OperEx(TlaFunOper.tuple, args @ _*) =>
      if (args.isEmpty) {
        // Surprisingly, somebody has written UNCHANGED << >>, see issue #475.
        Seq()
      } else {
        args.map(flattenTuplesInUnchanged).reduce(_ ++ _)
      }

    case ValEx(_) =>
      Seq() // no point in priming literals

    case _ =>
      // in general, UNCHANGED e becomes e' = e
      Seq(ex)
  }

  private def expandExceptOne(topFun: TlaEx, accessor: TlaEx, newValue: TlaEx): Seq[TlaOperDecl] = {
    // rewrite [ f EXCEPT ![i_1]...[i_n] = e ]
    def rewrite(fun: TlaEx, keys: List[TlaEx]): Seq[TlaOperDecl] = {
      keys match {
        case Nil =>
          throw new LirError("Expected at least one key in EXCEPT, found none")

        case hd :: Nil =>
          val uniqueName = gen.newName()
          // LET tmp == [ fun EXCEPT ![i_n] = e ] IN
          val decl = tla.declOp(uniqueName, tla.except(fun, hd, newValue)).untypedOperDecl()
          Seq(decl)

        case hd :: tl =>
          // fun[a_i]
          val nested = tla.appFun(fun, hd).untyped()
          // produce the expression for: [ fun[a_i] EXCEPT ![a_{i+1}]...[a_n] = e ]
          val defs = rewrite(nested, tl)
          // LET tmp == [ fun EXCEPT ![a_i] = output ] IN
          // tmp()
          val uniqueName = gen.newName()
          val nestedFun = tla.appOp(tla.name(defs.last.name)).untyped()
          val outDef = tla.declOp(uniqueName, tla.except(fun, hd, nestedFun)).untypedOperDecl()
          defs :+ outDef
      }
    }

    accessor match {
      case OperEx(TlaFunOper.tuple, keys @ _*) =>
        rewrite(topFun, keys.toList)

      case _ =>
        throw new LirError("Expected a tuple of keys as an accessor in EXCEPT. Found: " + accessor)
    }
  }

  private def expandExcept(fun: TlaEx, accessors: Seq[TlaEx], newValues: Seq[TlaEx]): TlaEx = {
    // The general case of [f EXCEPT !a_1 = e_1, ..., !a_n = e_n]
    // See p. 304 in Specifying Systems. The definition of EXCEPT for multiple accessors is doubly inductive.
    assert(accessors.length == newValues.length)
    val uniqueName = gen.newName()
    // LET tmp == fun IN
    val firstDef = tla.declOp(uniqueName, fun).untypedOperDecl()

    val defs =
      accessors.zip(newValues).foldLeft(Seq(firstDef)) { case (defs, (a, e)) =>
        val latest = tla.appOp(tla.name(defs.last.name)).untyped()
        defs ++ expandExceptOne(latest, a, e)
      }

    tla.letIn(tla.appOp(tla.name(defs.last.name)), defs: _*)
  }

  /**
   * Transform filter expressions like {<< x, y >> \in S: x = 1} to { x_y \in S: x_y[1] = 1 }
   *
   * @param boundEx a bound expression, e.g., x or << x, y >>
   * @param setEx   a set expression, e.g., S
   * @param predEx  a predicate expression, e.g., x == 1
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
   *
   * @param mapEx the mapping, e.g., x
   * @param args  bindings and sets
   * @return transformed arguments
   */
  def collapseTuplesInMap(mapEx: TlaEx, args: Seq[TlaEx]): Seq[TlaEx] = {
    val (boundEs, setEs) = TlaOper.deinterleave(args)
    val boundNames = boundEs map mkTupleName // rename tuples into a names, if needed
    // variable substitutions for the variables inside the tuples
    val subs = boundEs.foldLeft(Map[String, TlaEx]())(collectSubstitutions)
    val newMapEx = substituteNames(subs, mapEx)
    // collect the arguments back
    newMapEx +: TlaOper.interleave(boundNames.map(NameEx(_)), setEs)
  }

  private def collectSubstitutions(subs: Map[String, TlaEx], ex: TlaEx): Map[String, TlaEx] = {
    ex match {
      case NameEx(_) => subs // nothing to do

      case OperEx(TlaFunOper.tuple, _*) =>
        val tupleName = mkTupleName(ex) // introduce a name, e.g., x_y_z for <<x, <<y, z>> >>
        val indices = assignIndicesInTuple(Map(), ex, Seq())

        def indexToTlaEx(index: Seq[Int]): TlaEx = {
          index.foldLeft(tla.name(tupleName): TlaEx) { (e, i) =>
            tla.appFun(e, tla.int(i))
          }
        }

        // map every variable inside the tuple to a tuple access, e.g., x -> x_y_z[1] and z -> x_y_z[1][2]
        indices.foldLeft(subs) { (m, p) =>
          m + (p._1 -> indexToTlaEx(p._2))
        }

      case _ =>
        throw new IllegalArgumentException("Unexpected %s among set filter parameters".format(ex))
    }
  }

  private def mkTupleName(ex: TlaEx): String = {
    ex match {
      case NameEx(name) => name

      case OperEx(TlaFunOper.tuple, args @ _*) =>
        (args map mkTupleName) mkString "_"

      case _ =>
        throw new IllegalArgumentException("Unexpected %s among set filter parameters".format(ex))
    }
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

      case LetInEx(body, defs @ _*) =>
        val newDefs = defs.map(d => d.copy(body = rename(d.body)))
        LetInEx(rename(body), newDefs: _*)(e.typeTag)

      case OperEx(op, args @ _*) =>
        OperEx(op, args map rename: _*)(e.typeTag)

      case _ => e
    }

    rename(ex)
  }
}

object Desugarer {
  def apply(gen: UniqueNameGenerator, tracker: TransformationTracker): Desugarer = {
    new Desugarer(gen, tracker)
  }
}
