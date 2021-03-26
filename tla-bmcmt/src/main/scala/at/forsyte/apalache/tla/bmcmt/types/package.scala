package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.{
  BoolT1, ConstT1, FunT1, IntT1, NullEx, OperT1, RealT1, RecT1, SeqT1, SetT1, SparseTupT1, StrT1, TlaType1, TupT1,
  TypeTag, TypingException, VarT1
}

import scala.collection.immutable.SortedMap

package object types {
  // @Jure 29.10.2017: Change name, too ambiguous, especially with TLA Types in the other package -- Jure, 29.10.17
  // @Igor 05.01.2019: What is the problem? The full package name is at.forsyte.apalache.tla.bmcmt.types.

  /**
   * A simple type system for the symbolic memory cells.
   */
  sealed abstract class CellT extends Serializable {

    /**
     * Test whether two types may produce objects that are comparable.
     *
     * @param other other type
     * @return true, if objects of the given types may be comparable
     */
    def comparableWith(other: CellT): Boolean = {
      this.unify(other).nonEmpty
    }

    /**
     * Produce a short signature that uniquely describes the type (up to unification),
     * similar to Java's signature mangling. If one type can be unified to another,
     * e.g., records, they have the same signature.
     *
     * @return a short signature that uniquely characterizes this type up to unification
     */
    val signature: String

    /**
     * Convert the cell type into TlaType1. Note that
     *
     * @return
     */
    def toTlaType1: TlaType1

    /**
     * Compute a unifier of two types.
     *
     * @param other another type
     * @return Some(unifier), if there is one, or None otherwise
     */
    def unify(other: CellT): Option[CellT] = {
      (this, other) match {
        case (UnknownT(), _) =>
          Some(other)

        case (_, UnknownT()) =>
          Some(this)

        case (BoolT(), BoolT()) | (ConstT(), ConstT()) | (IntT(), IntT()) =>
          Some(this)

        case (FinSetT(left), FinSetT(right)) =>
          left.unify(right) map FinSetT

        case (InfSetT(left), InfSetT(right)) =>
          left.unify(right) map InfSetT

        case (FunT(leftDom, leftCodom), FunT(rightDom, rightCodom)) =>
          for {
            domUnif <- leftDom.unify(rightDom)
            cdmUnif <- leftCodom.unify(rightCodom)
          } yield FunT(domUnif, cdmUnif)

        case (FinFunSetT(leftDom, leftCdm), FinFunSetT(rightDom, rightCdm)) =>
          for {
            domUnif <- leftDom.unify(rightDom)
            cdmUnif <- leftCdm.unify(rightCdm)
          } yield FinFunSetT(domUnif, cdmUnif)

        case (PowSetT(left), PowSetT(right)) =>
          left.unify(right) map PowSetT

        case (SeqT(left), SeqT(right)) =>
          left.unify(right) map SeqT

        case (SeqT(seqType), TupleT(tupleTypes)) =>
          types.unify(seqType +: tupleTypes: _*) match {
            case Some(et) => Some(SeqT(et))
            case None     => None
          }

        case (TupleT(tupleTypes), SeqT(seqType)) =>
          types.unify(seqType +: tupleTypes: _*) match {
            case Some(et) => Some(SeqT(et))
            case None     => None
          }

        /**
         * Jure, 13.9.18: Suggestion: Change TupleT( _ : Seq[...]) to TupleT(_ : Array[...]) or
         * TupleT( _ : IndextSeq[...]) so
         * a) length checks are const time
         * b) you can do index-based arg comparison
         */
        case (TupleT(leftArgs), TupleT(rightArgs)) =>
          // in contrast to sequences, tuples of different lengths cannot be unified
          if (leftArgs.lengthCompare(rightArgs.length) == 0) {
            val unified = leftArgs.zip(rightArgs) map (p => p._1.unify(p._2))
            if (unified.forall(_.isDefined)) {
              Some(TupleT(unified.map(_.get)))
            } else {
              None
            }
          } else {
            None
          }

        case (RecordT(leftMap), RecordT(rightMap)) =>
          // records that have different keys can be unified
          def unifyKey(key: String): Option[CellT] = {
            (leftMap.get(key), rightMap.get(key)) match {
              case (Some(l), Some(r)) =>
                l.unify(r)

              case (Some(l), None) =>
                Some(l)

              case (None, Some(r)) =>
                Some(r)

              case _ =>
                None
            }
          }

          val pairs = leftMap.keySet.union(rightMap.keySet).map(k => (k, unifyKey(k)))

          if (pairs.exists(_._2.isEmpty)) {
            None
          } else {
            val somes = pairs.map { case (k, v) => (k, v.get) } // (p => (p._1, p._2.get))
            Some(RecordT(SortedMap(somes.toSeq: _*)))
          }

        case _ =>
          None
      }
    }
  }

  object CellT {

    /**
     * Convert a TlaType1 to a cell type.
     */
    def fromType1(tt: TlaType1): CellT = {
      tt match {
        case IntT1()    => IntT()
        case StrT1()    => ConstT()
        case BoolT1()   => BoolT()
        case ConstT1(_) => ConstT() // this should change in https://github.com/informalsystems/apalache/issues/570
        case RealT1() =>
          throw new TypingException("Unsupported type RealT1")

        case VarT1(_) =>
          // type variables should have been resolved by operator inlining and type checking
          throw new TypingException("Unexpected type VarT1")

        case SetT1(elem)       => FinSetT(fromType1(elem))
        case SeqT1(elem)       => SeqT(fromType1(elem))
        case FunT1(arg, res)   => FunT(FinSetT(fromType1(arg)), fromType1(res))
        case TupT1(elems @ _*) => TupleT(elems.map(fromType1))
        case RecT1(fieldTypes) => RecordT(fieldTypes.mapValues(fromType1))

        case SparseTupT1(_) =>
          // sparse tuple can only appear in operator arguments, which must have been inlined
          throw new TypingException("Unexpected type SparseTupT1")

        case OperT1(_, _) =>
          // all operators are inlined
          throw new TypingException("Unexpected operator type OperT1")
      }
    }

    /**
     * Convert a type tag to a cell type
     *
     * @param typeTag a type tag
     * @return the corresponding cell type, if the tag has type Typed(_: TlaType1); otherwise, throw an exception
     */
    def fromTypeTag(typeTag: TypeTag): CellT = {
      fromType1(TlaType1.fromTypeTag(typeTag))
    }

  }

  // Jure @ 13.09.18: Suggestion: Replace all case class X( [no args] ) with object X ?
  //
  // Igor @ 20.12.18: This is called preliminary optimization. I would imagine that the scala
  // compiler would do that for case classes, since they are thought-of as immutable.
  // However, a simple test in the debugger shows that a new object is created, whenever
  // an empty-parameter case class is constructed. Weird. However, let's do this optimization,
  // only if it becomes a bottleneck. At this stage, clarity is more important.

  /**
   * A type variable.
   */
  sealed case class UnknownT() extends CellT with Serializable {

    /**
     * Produce a short signature that uniquely describes the type (up to unification),
     * similar to Java's signature mangling. If one type can be unified to another,
     * e.g., records, they have the same signature.
     *
     * @return a short signature that uniquely characterizes this type up to unification
     */
    override val signature: String = "u"

    override val toString: String = "Unknown"

    override def toTlaType1: TlaType1 = {
      ConstT1("UNKNOWN")
    }
  }

  /**
   * A cell constant, that is, just a name that expresses string constants in TLA+.
   */
  sealed case class ConstT() extends CellT with Serializable {
    override val signature: String = "str"

    override val toString: String = "Const"

    override def toTlaType1: TlaType1 = {
      // in the new type system, we have the string type for such constants
      StrT1()
    }
  }

  /**
   * A Boolean cell type.
   */
  sealed case class BoolT() extends CellT with Serializable {
    override val signature: String = "b"

    override val toString: String = "Bool"

    override def toTlaType1: TlaType1 = BoolT1()
  }

  /**
   * An integer cell type.
   */
  sealed case class IntT() extends CellT with Serializable {
    override val signature: String = "i"

    override val toString: String = "Int"

    override def toTlaType1: TlaType1 = IntT1()
  }

  /**
   * A finite set.
   *
   * @param elemType the elements type
   */
  sealed case class FinSetT(elemType: CellT) extends CellT with Serializable {
    override val signature: String = s"S${elemType.signature}"

    override val toString: String = s"FinSet[$elemType]"

    override def toTlaType1: TlaType1 = SetT1(elemType.toTlaType1)
  }

  /**
   * An infinite set such as Nat or Int. Although the rewriting system expands only finite sets,
   * in some cases, we can pick a value from an infinite set, e.g., \E x \in Int: P.
   *
   * @param elemType the elements type
   */
  sealed case class InfSetT(elemType: CellT) extends CellT with Serializable {
    override val signature: String = s"Z${elemType.signature}"

    override val toString: String = s"InfSet[$elemType]"

    override def toTlaType1: TlaType1 = SetT1(elemType.toTlaType1)
  }

  /**
   * The type of a powerset of a finite set, which is constructed as 'SUBSET S' in TLA+.
   * @param domType the type of the argument is a finite set, i.e., typeof(S) in SUBSET S.
   *                Currently, only FinSetT(_) is supported.
   */
  sealed case class PowSetT(domType: CellT) extends CellT with Serializable {
    require(domType.isInstanceOf[FinSetT]) // currently, we support only PowSetT(FinSetT(_))

    override val signature: String = s"P${domType.signature}"

    override val toString: String = s"PowSet[$domType]"

    override def toTlaType1: TlaType1 = SetT1(domType.toTlaType1)
  }

  /**
   * A function type.
   *
   * TODO: in the future, we will replace domType with argType, as we are moving towards
   * a minimalistic type system
   *
   * @param domType    the type of the domain (a finite set, a powerset, or a cross product).
   * @param resultType result type (not the co-domain!)
   */
  sealed case class FunT(domType: CellT, resultType: CellT) extends CellT with Serializable {
    override val signature: String = s"f${domType.signature}_${resultType.signature}"

    val argType: CellT = domType match {
      case FinSetT(et) => et
      case PowSetT(dt) => dt
      case _           => throw new TypeException(s"Unexpected domain type $domType", NullEx)
    }

    override val toString: String = s"Fun[$domType, $resultType]"

    override def toTlaType1: TlaType1 = {
      domType.toTlaType1 match {
        case SetT1(elemType) => FunT1(elemType, resultType.toTlaType1)
        case tt              => throw new TypingException("Unexpected function domain type: " + tt)
      }
    }
  }

  /**
   * A finite set of functions.
   *
   * @param domType the type of the domain (must be either a finite set or a powerset).
   * @param cdmType the type of the co-domain (must be either a finite set or a powerset).
   */
  sealed case class FinFunSetT(domType: CellT, cdmType: CellT) extends CellT with Serializable {
    require(
        (domType.isInstanceOf[FinSetT] || domType.isInstanceOf[PowSetT])
          && (cdmType.isInstanceOf[FinSetT] || cdmType.isInstanceOf[PowSetT]
            || cdmType.isInstanceOf[FinFunSetT] || cdmType.isInstanceOf[InfSetT]))

    override val signature: String = s"F%${domType.signature}_%${cdmType.signature}"

    def argType(): CellT = domType match {
      case FinSetT(et) => et
      case PowSetT(dt) => dt
      case _           => throw new TypeException(s"Unexpected domain type $domType", NullEx)
    }

    def resultType(): CellT = cdmType match {
      case FinSetT(et) => et
      case PowSetT(dt) => dt
      case _           => throw new TypeException(s"Unexpected co-domain type $cdmType", NullEx)
    }

    override val toString: String = s"FinFunSet[$domType, $cdmType]"

    override def toTlaType1: TlaType1 = {
      (domType.toTlaType1, cdmType.toTlaType1) match {
        case (SetT1(arg), SetT1(res)) => SetT1(FunT1(arg, res))
        case (dt, cdt)                => throw new TypingException(s"Unexpected domain type $dt and result type $cdt")
      }
    }
  }

  /**
   * A tuple type
   *
   * @param args the types of the tuple elements
   */
  sealed case class TupleT(args: Seq[CellT]) extends CellT with Serializable {

    override val signature: String = s"T_${args.map(_.signature).mkString("_")}"

    override val toString: String = s"Tuple[${args.map(_.toString).mkString(", ")}]"

    override def toTlaType1: TlaType1 = {
      TupT1(args.map(_.toTlaType1): _*)
    }
  }

  /**
   * A sequence type. Note that in contrast to the standard TLA+ semantics,
   * we distinguish tuples and sequences. The difference is that a tuple can have
   * elements of different types, while a sequence has only elements of the same type.
   *
   * @param res the type of the elements in the co-domain
   */
  sealed case class SeqT(res: CellT) extends CellT with Serializable {

    override val signature: String = s"Q_${res.signature}"

    override val toString: String = s"Seq[$res]"

    override def toTlaType1: TlaType1 = SeqT1(res.toTlaType1)
  }

  /**
   * A record type
   *
   * @param fields a map of fields and their types
   */
  sealed case class RecordT(fields: SortedMap[String, CellT]) extends CellT with Serializable {
    override val signature: String = "R"

    override val toString: String =
      s"Record[${fields.map { case (k, v) => "\"" + k + "\" -> " + v } mkString ", "}]"

    override def toTlaType1: TlaType1 = {
      RecT1(fields.mapValues(_.toTlaType1))
    }
  }

  /**
   * Unify two types decorated with Option.
   *
   * @param left a left type (may be None)
   * @param right a right type (may be None)
   * @return Some(unifier), if there is one, otherwise None
   */
  def unifyOption(left: Option[CellT], right: Option[CellT]): Option[CellT] = for {
    l <- left
    r <- right
    u <- l.unify(r)
  } yield u

  /**
   * Unify a sequence of types
   * @param ts a sequence of types
   * @return Some(unifier), if exists, or None
   */
  def unify(ts: CellT*): Option[CellT] =
    ts.map(Some(_)).reduce[Option[CellT]]((x, y) => unifyOption(x, y))

}
