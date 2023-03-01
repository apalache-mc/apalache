package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir._

/**
 * @author
 *   Jure Kukovec
 */
package object types {

  /**
   * A simple type system for the symbolic memory cells.
   */
  sealed abstract class CellT extends Serializable {

    // Prive an odering for CellT so we can build SortedMaps
    implicit val cellTOrdering: Ordering[CellT] = new Ordering[CellT] {
      def compare(a: CellT, b: CellT): Int = a.signature.compare(b.signature)
    }

    /**
     * Produce a short signature that uniquely describes the type (up to unification), similar to Java's signature
     * mangling. If one type can be unified to another, e.g., records, they have the same signature.
     *
     * @return
     *   a short signature that uniquely characterizes this type up to unification
     */
    val signature: String

    /**
     * Convert the cell type into TlaType1. Note that
     *
     * @return
     */
    def toTlaType1: TlaType1
  }

  object CellT {

    /**
     * Convert a TlaType1 to a cell type.
     */
    def fromType1(tt: TlaType1): CellT = {
      tt match {
        case RealT1 =>
          throw new TypingException("Unsupported type RealT1", UID.nullId)

        case VarT1(_) =>
          // type variables should have been resolved by operator inlining and type checking
          throw new TypingException("Unexpected type VarT1", UID.nullId)

        case SparseTupT1(_) =>
          // sparse tuple can only appear in operator arguments, which must have been inlined
          throw new TypingException("Unexpected type SparseTupT1", UID.nullId)

        case OperT1(_, _) =>
          // all operators are inlined
          throw new TypingException("Unexpected operator type OperT1", UID.nullId)

        case RecRowT1(RowT1(_, None)) | VariantT1(RowT1(_, None)) =>
          CellTFrom(tt)

        case RecRowT1(RowT1(_, _)) =>
          throw new TypingException("Polymorphic records are not supported by the model checker", UID.nullId)

        case VariantT1(RowT1(_, _)) =>
          throw new TypingException("Polymorphic variants are not supported by the model checker", UID.nullId)

        case RowT1(_, _) =>
          throw new TypingException("Polymorphic rows are not supported by the model checker", UID.nullId)

        case tt => CellTFrom(tt)
      }
    }

    /**
     * Convert a type tag to a cell type
     *
     * @param typeTag
     *   a type tag
     * @return
     *   the corresponding cell type, if the tag has type Typed(_: TlaType1); otherwise, throw an exception
     */
    def fromTypeTag(typeTag: TypeTag): CellT = {
      fromType1(TlaType1.fromTypeTag(typeTag))
    }

  }

  /**
   * A type variable.
   */
  sealed case class UnknownT() extends CellT with Serializable {

    /**
     * Produce a short signature that uniquely describes the type (up to unification), similar to Java's signature
     * mangling. If one type can be unified to another, e.g., records, they have the same signature.
     *
     * @return
     *   a short signature that uniquely characterizes this type up to unification
     */
    override val signature: String = "u"

    override val toString: String = "Unknown"

    override def toTlaType1: TlaType1 = {
      ConstT1("UNKNOWN")
    }
  }

  sealed case class CellTFrom(tt: TlaType1) extends CellT with Serializable {
    override val signature: String = tt match {
      case ConstT1(utype)     => s"UT_$utype"
      case StrT1              => "UT_Str"
      case BoolT1             => "b"
      case IntT1              => "i"
      case SetT1(et)          => s"S" + CellTFrom(et).signature
      case SeqT1(et)          => "Q_" + CellTFrom(et).signature
      case FunT1(argT, resT)  => "f%s_%s".format(CellTFrom(argT).signature, CellTFrom(resT).signature)
      case TupT1(elemsT @ _*) => "T_" + elemsT.map(et => CellTFrom(et).signature).mkString("_")
      case RecT1(_)           => "R"
      case _                  => "U"
    }

    override def toTlaType1: TlaType1 = tt
  }

  /**
   * An infinite set such as Nat or Int. Although the rewriting system expands only finite sets, in some cases, we can
   * pick a value from an infinite set, e.g., \E x \in Int: P.
   *
   * @param elemType
   *   the elements type
   */
  sealed case class InfSetT(elemType: CellT) extends CellT with Serializable {
    override val signature: String = s"Z${elemType.signature}"

    override val toString: String = s"InfSet[$elemType]"

    override def toTlaType1: TlaType1 = SetT1(elemType.toTlaType1)
  }

  /**
   * The type of a powerset of a finite set, which is constructed as 'SUBSET S' in TLA+.
   *
   * @param domType
   *   the type of the argument is a finite set, i.e., typeof(S) in SUBSET S. Currently, only FinSetT(_) is supported.
   */
  sealed case class PowSetT(domType: TlaType1) extends CellT with Serializable {
    require(domType.isInstanceOf[SetT1]) // currently, we support only PowSetT(FinSetT(_))

    override val signature: String = s"P" + CellTFrom(domType).signature

    override val toString: String = s"PowSet[$domType]"

    override def toTlaType1: TlaType1 = SetT1(domType)
  }

  /**
   * A finite set of functions.
   *
   * @param domType
   *   the type of the domain (must be either a finite set or a powerset).
   * @param cdmType
   *   the type of the co-domain (must be either a finite set or a powerset).
   */
  sealed case class FinFunSetT(domType: CellT, cdmType: CellT) extends CellT with Serializable {
    require(domType match {
          case CellTFrom(SetT1(_)) | PowSetT(_) => true
          case _                                => false
        }, "The right-hand side of a function set should be: a finite set or a powerset")
    require(cdmType match {
          case CellTFrom(SetT1(_)) | PowSetT(_) | FinFunSetT(_, _) | InfSetT(_) => true
          case _                                                                => false
        }, "The right-hand side of a function set should be: a finite/infinite set, a powerset, or a function set")

    override val signature: String = s"F%${domType.signature}_%${cdmType.signature}"

    def argType(): TlaType1 = domType match {
      case CellTFrom(SetT1(et)) => et
      case PowSetT(dt)          => dt
      case _                    => throw new TypingException(s"Unexpected domain type $domType", UID.nullId)
    }

    def resultType(): TlaType1 = cdmType match {
      case CellTFrom(SetT1(et)) => et
      case PowSetT(dt)          => dt
      case _                    => throw new TypingException(s"Unexpected co-domain type $cdmType", UID.nullId)
    }

    override val toString: String = s"FinFunSet[$domType, $cdmType]"

    override def toTlaType1: TlaType1 = {
      (domType.toTlaType1, cdmType.toTlaType1) match {
        case (SetT1(arg), SetT1(res)) =>
          SetT1(FunT1(arg, res))

        case (dt, cdt) =>
          throw new TypingException(s"Unexpected domain type $dt and result type $cdt", UID.nullId)
      }
    }
  }
}
