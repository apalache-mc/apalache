package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import TypedPredefs._

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
      val transformedArgs = args.map(transform(_))
      val asTuple = tla
        .tuple(transformedArgs: _*)
        .typed(TupT1(transformedArgs.map(_.typeTag.asTlaType1()): _*))
      val flatArgs = flattenTuplesInUnchanged(asTuple)
      // map every x to x' = x
      val eqs = flatArgs map { x: TlaEx =>
        val tt = x.typeTag.asTlaType1()
        val xb = tla.fromTlaEx(x)
        tla
          .eql(tla.prime(xb) ? "x", xb)
          .typed(Map("b" -> BoolT1(), "x" -> tt), "b")
      }
      // x' = x /\ y' = y /\ z' = z
      eqs match {
        case Seq() =>
          // results from UNCHANGED <<>>, UNCHANGED << << >> >>, etc.
          tla.bool(true).typed()

        case Seq(one) =>
          one

        case _ =>
          tla.and(eqs: _*).typed(BoolT1())
      }

    case OperEx(TlaOper.eq, OperEx(TlaFunOper.tuple, largs @ _*), OperEx(TlaFunOper.tuple, rargs @ _*)) =>
      // <<e_1, ..., e_k>> = <<f_1, ..., f_n>>
      // produce pairwise comparison
      if (largs.length != rargs.length) {
        tla.bool(false).typed()
      } else {
        val eqs = largs.zip(rargs) map { case (l, r) => tla.eql(this(l), this(r)).typed(BoolT1()) }
        tla.and(eqs: _*).typed(BoolT1())
      }

    case OperEx(TlaOper.ne, OperEx(TlaFunOper.tuple, largs @ _*), OperEx(TlaFunOper.tuple, rargs @ _*)) =>
      // <<e_1, ..., e_k>> /= <<f_1, ..., f_n>>
      // produce pairwise comparison
      if (largs.length != rargs.length) {
        tla.bool(true).typed()
      } else {
        val neqs = largs.zip(rargs) map { case (l, r) => tla.neql(this(l), this(r)).typed(BoolT1()) }
        tla.or(neqs: _*).typed(BoolT1())
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
          val pointType = TupT1(vars.map(_.typeTag.asTlaType1()): _*)
          val point = tla.tuple(vars: _*).typed(pointType)
          val plane = tla.times(sets: _*).typed(SetT1(pointType))
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
          val funT = fun.typeTag.asTlaType1() // either FunT1, RecT1, TupT1, or SeqT1
          val operT = OperT1(Seq(), funT)
          val decl = tla
            .declOp(uniqueName, tla.except(fun, tla.tuple(hd).typed(hd.typeTag.asTlaType1()), newValue).typed(funT))
            .typedOperDecl(operT)
          Seq(decl)

        case hd :: tl =>
          // fun[a_i]
          val funT = fun.typeTag.asTlaType1() // either FunT1, RecT1, TupT1, or SeqT1
          val operT = OperT1(Seq(), funT)
          val (_, resT) = eatFunType(funT, hd)
          val nested = tla.appFun(fun, hd).typed(resT)
          // produce the expression for: [ fun[a_i] EXCEPT ![a_{i+1}]...[a_n] = e ]
          val defs = rewrite(nested, tl)
          // LET tmp == [ fun EXCEPT ![a_i] = output ] IN
          // tmp()
          val uniqueName = gen.newName()
          val nestedFun = tla
            .appOp(tla.name(defs.last.name) ? "F")
            .typed(Map("F" -> operT, "r" -> resT), "r")
          val outDef = tla
            .declOp(uniqueName, tla.except(fun, tla.tuple(hd).typed(hd.typeTag.asTlaType1()), nestedFun).typed(funT))
            .typedOperDecl(operT)
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
    val funT = fun.typeTag.asTlaType1()
    // LET tmp == fun IN
    val firstDef = tla.declOp(uniqueName, fun).typedOperDecl(OperT1(Seq(), funT))

    val defs =
      accessors.zip(newValues).foldLeft(Seq(firstDef)) { case (defs, (a, e)) =>
        val last = defs.last
        val latest = tla.appOp(NameEx(last.name)(last.typeTag)).typed(funT)
        defs ++ expandExceptOne(latest, a, e)
      }

    val operT = OperT1(Seq(), funT)
    tla
      .letIn(tla.appOp(tla.name(defs.last.name) ? "F") ? "f", defs: _*)
      .typed(Map("F" -> operT, "f" -> funT), "f")
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
    val xtype = boundEx.typeTag.asTlaType1()
    Seq(tla.name(boundName).typed(xtype), setEx, newPred)
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
    val boundNames = boundEs map { e =>
      val tupleName = mkTupleName(e)
      NameEx(tupleName)(e.typeTag)
    } // rename tuples into a names, if needed
    // variable substitutions for the variables inside the tuples
    val subs = boundEs.foldLeft(Map[String, TlaEx]())(collectSubstitutions)
    val newMapEx = substituteNames(subs, mapEx)
    // collect the arguments back
    newMapEx +: TlaOper.interleave(boundNames, setEs)
  }

  // this looks like a useful utility function. Move it somewhere else?
  private def eatFunType(funT: TlaType1, arg: TlaEx): (TlaType1, TlaType1) = {
    (funT, arg) match {
      case (FunT1(argT, resT), _) =>
        if (Typed(argT) != arg.typeTag) {
          val actualArgType = arg.typeTag.asTlaType1()
          throw new TypingException(s"Expected a function argument of type $argT, found $actualArgType")
        } else {
          (argT, resT)
        }

      case (SeqT1(elem), _) =>
        if (Typed(IntT1()) != arg.typeTag) {
          val actualArgType = arg.typeTag.asTlaType1()
          throw new TypingException(s"Expected a sequence argument to be an integer, found $actualArgType")
        } else {
          (IntT1(), elem)
        }

      case (tt @ RecT1(fieldTypes), ValEx(TlaStr(key))) =>
        if (fieldTypes.contains(key)) {
          (StrT1(), fieldTypes(key))
        } else {
          throw new IllegalArgumentException(s"No key $key in $tt")
        }

      case (tt @ RecT1(_), _) =>
        throw new TypingException(s"Expected a string argument for $tt, found: $arg")

      case (tt @ TupT1(elems @ _*), ValEx(TlaInt(index))) =>
        if (index > 0 && index <= elems.length) {
          (IntT1(), elems(index.toInt - 1))
        } else {
          throw new IllegalArgumentException(s"No index $index in $tt")
        }

      case (tt @ TupT1(_), _) =>
        throw new TypingException(s"Expected a string argument for $tt, found: $arg")

      case _ =>
        throw new TypingException(s"Unexpected type in function application: $arg")
    }
  }

  private def collectSubstitutions(subs: Map[String, TlaEx], ex: TlaEx): Map[String, TlaEx] = {
    ex match {
      case NameEx(_) => subs // nothing to do

      case OperEx(TlaFunOper.tuple, _*) =>
        val tupleName = mkTupleName(ex) // introduce a name, e.g., x_y_z for <<x, <<y, z>> >>
        val indices = assignIndicesInTuple(Map(), ex, Seq())

        def indexToTlaEx(indices: Seq[Int]): TlaEx = {
          indices.foldLeft(NameEx(tupleName)(ex.typeTag): TlaEx) { case (e, i) =>
            val index = tla.int(i).typed()
            val (_, resT) = eatFunType(e.typeTag.asTlaType1(), index)
            tla.appFun(e, index).typed(resT)
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
