package at.forsyte.apalache.tla.bmcmt

import scala.collection.immutable.SortedMap

/** Change name, too ambiguous, especially with TLA Types in the other package -- Jure, 29.10.17 */
package object types {

  /**
    * A simple type system for the symbolic memory cells.
    */
  sealed abstract class CellT {
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
//          val unif = left.unify(right)
//          if (unif.nonEmpty) Some(FinSetT(unif.get)) else None

        case (FunT(leftDom, leftCodom), FunT(rightDom, rightCodom)) =>
          for {
            domUnif <- leftDom.unify(rightDom)
            cdmUnif <- leftCodom.unify(rightCodom)
          } yield FunT(domUnif, cdmUnif)

//          val domUnif = leftDom.unify(rightDom)
//          val cdmUnif = leftCodom.unify(rightCodom)
//
//
//          if (domUnif.nonEmpty && cdmUnif.nonEmpty) {
//            Some(FunT(domUnif.get, cdmUnif.get))
//          } else {
//            None
//          }

        case (FinFunSetT(leftDom, leftCdm), FinFunSetT(rightDom, rightCdm)) =>
          for {
            domUnif <- leftDom.unify(rightDom)
            cdmUnif <- leftCdm.unify(rightCdm)
          } yield FinFunSetT(domUnif, cdmUnif)
//
//          val domUnif = leftDom.unify(rightDom)
//          val cdmUnif = leftCdm.unify(rightCdm)
//          if (domUnif.nonEmpty && cdmUnif.nonEmpty) {
//            Some(FinFunSetT(domUnif.get, cdmUnif.get))
//          } else {
//            None
//          }

        case (PowSetT(left), PowSetT(right)) =>
          left.unify(right) map PowSetT
//          val domUnif = left.unify(right)
//          if (domUnif.nonEmpty)
//            Some(PowSetT(domUnif.get))
//          else
//            None

          /**
            * Jure, 13.9.18: Suggestion: Change TupleT( _ : Seq[...]) to TupleT(_ : Array[...]) or
            * TupleT( _ : IndextSeq[...]) so
            * a) length checks are const time
            * b) you can do index-based arg comparison
            * */
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
            val somes = pairs.map { case (k, Some(v)) => (k,v) } // (p => (p._1, p._2.get))
            Some(RecordT(SortedMap(somes.toSeq: _*)))
          }

        case _ =>
          None
      }
    }
  }


  /**
    * Jure, 13.9.18: Suggestion: Replace all case class X( [no args] ) with object X ?
    * */

  /**
    * A type variable.
    */
  sealed case class UnknownT() extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = "u"

    override val toString: String = "Unknown"
  }

  /**
    * A failure cell that represents a Boolean variable indicating whether
    * a certain operation failed.
    */
  sealed case class FailPredT() extends CellT {
    override val signature: String = "E"

    override val toString: String = "FailPred"
  }

  /**
    * A cell constant, that is, just a name that expresses string constants in TLA+.
    */
  sealed case class ConstT() extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = "str"

    override val toString: String = "Const"
  }

  /**
    * A Boolean cell type.
    */
  sealed case class BoolT() extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = "b"

    override val toString: String = "Bool"
  }

  /**
    * An integer cell type.
    */
  sealed case class IntT() extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = "i"

    override val toString: String = "Int"
  }

  /**
    * A finite set.
    *
    * @param elemType the elements type
    */
  sealed case class FinSetT(elemType: CellT) extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = s"S${elemType.signature}"

    override val toString: String = s"FinSet[$elemType]"
  }

  /**
    * The type of a powerset of finite set, which is constructed as 'SUBSET S' in TLA+.
    * @param domType the type of the argument finite set, i.e., typeof(S) in SUBSET S.
    *                Currently, only FinSetT(_) is supported.
    */
  sealed case class PowSetT(domType: CellT) extends CellT {
    require(domType.isInstanceOf[FinSetT]) // currently, we support only PowSetT(FinSetT(_))
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = s"P${domType.signature}"

    override val toString: String = s"PowSet[$domType]"
  }

  /**
    * A function type.
    *
    * @param domType    the type of the domain (must be a finite set).
    * @param resultType result type (not co-domain!)
    */
  sealed case class FunT(domType: CellT, resultType: CellT) extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = s"f${domType.signature}_${resultType.signature}"
//    override val signature: String = "f%s_%s".format(domType.signature, resultType.signature)

    val argType: CellT = domType match {
      case FinSetT(et) => et
      case PowSetT(dt) => dt
      case _ => throw new TypeException(s"Unexpected domain type $domType")
    }

    override val toString: String = s"Fun[$domType, $resultType]"
  }

  /**
    * A finite set of functions.
    *
    * @param domType the type of the domain (must be either a finite set or a powerset).
    * @param cdmType the type of the co-domain (must be either a finite set or a powerset).
    */
  sealed case class FinFunSetT(domType: CellT, cdmType: CellT) extends CellT {
    require((domType.isInstanceOf[FinSetT] || domType.isInstanceOf[PowSetT])
            && (cdmType.isInstanceOf[FinSetT] || cdmType.isInstanceOf[PowSetT]))
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = s"F%${domType.signature}_%${cdmType.signature}"

    def argType(): CellT = domType match {
      case FinSetT(et) => et
      case PowSetT(dt) => dt
      case _ => throw new TypeException(s"Unexpected domain type $domType")
    }

    def resultType(): CellT = cdmType match {
      case FinSetT(et) => et
      case PowSetT(dt) => dt
      case _ => throw new TypeException(s"Unexpected co-domain type $cdmType")
    }

    override val toString: String = s"FinFunSet[$domType, $cdmType]"
  }

  /**
    * A tuple type
    *
    * @param args the types of the tuple elements
    */
  sealed case class TupleT(args: Seq[CellT]) extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = s"T_${args.map(_.signature).mkString("_")}"

    override val toString: String = s"Tuple[${args.map(_.toString).mkString(", ")}]"
  }

  /**
    * A record type
    *
    * @param fields a map of fields and their types
    */
  sealed case class RecordT(fields: SortedMap[String, CellT]) extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * As records having different domains can be unified, we do not include the records arguments in the signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature: String = "R"

    override val toString: String =
      s"Record[${fields.map {case (k,v) => "\"" + k + "\" -> " + v } mkString ", " }]"
  }


  sealed case class TypeParam(s: String) extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature = s"P${s}"
  }

  sealed case class OptT( elementType: CellT ) extends CellT {
    /**
      * Produce a short signature that uniquely describes the type (up to unification),
      * similar to Java's signature mangling. If one type can be unified to another,
      * e.g., records, they have the same signature.
      *
      * @return a short signature that uniquely characterizes this type up to unification
      */
    override val signature : String = s"O${elementType.signature}"
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
//  {
//    (left, right) match {
//      case (Some(l), Some(r)) =>
//        l.unify(r)
//
//      case _ =>
//        None
//    }
//  }

  /**
    * Unify a sequence of types
    * @param ts a sequence of types
    * @return Some(unifier), if exists, or None
    */
  def unify(ts: CellT*): Option[CellT] =
    ts.map(Some(_)).reduce[Option[CellT]]((x, y) => unifyOption(x, y))

}
