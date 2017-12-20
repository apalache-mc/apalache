package at.forsyte.apalache.tla.bmcmt

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
          val unif = left.unify(right)
          if (unif.nonEmpty) Some(FinSetT(unif.get)) else None

        case (FunT(leftDom, leftCodom), FunT(rightDom, rightCodom)) =>
          val domUnif = leftDom.unify(rightDom)
          val cdmUnif = leftCodom.unify(rightCodom)
          if (domUnif.nonEmpty && cdmUnif.nonEmpty) {
            Some(FunT(domUnif.get, cdmUnif.get))
          } else {
            None
          }

        case (TupleT(leftArgs), TupleT(rightArgs)) =>
          val maxlen = Math.max(leftArgs.length, rightArgs.length)
          val paddedPairs: Seq[(CellT, CellT)] = leftArgs.padTo(maxlen, UnknownT()).zip(rightArgs.padTo(maxlen, UnknownT()))
          val newArgs = paddedPairs map { case (l, r) => l.unify(r) }
          if (newArgs.exists(_.isEmpty))
            None
          else
            Some(TupleT(newArgs map (_.get)))

        case (RecordT(leftMap), RecordT(rightMap)) =>
          def unifyKey(key: String): Option[CellT] = {
            (leftMap.get(key), rightMap.get(key)) match {
              case (Some(l), Some(r)) =>
                l.unify(r)

              case (Some(l), None) =>
                Some(l)

              case (None, Some(r)) =>
                Some(r)
            }
          }
          val pairs = leftMap.keySet.union(rightMap.keySet).map(k => (k, unifyKey(k)))
          if (pairs.exists (_._2.isEmpty)) {
            None
          } else {
            val somes = pairs.map(p => (p._1, p._2.get))
            Some(RecordT(Map(somes.toSeq: _*)))
          }

        case _ =>
          None
      }
    }

    /**
      * Join with another type.
      *
      * @param other another type
      * @return a composite type, e.g., SumT(this, other)
      */
    def join(other: CellT): CellT = {
      (this, other) match {
        case (FinSetT(left), FinSetT(right)) =>
          FinSetT(left.join(right))

        case (SumT(leftTypes), SumT(rightTypes)) =>
          SumT(Set(leftTypes ++ rightTypes: _*).toList)

        case (SumT(leftTypes), _) =>
          SumT(Set(other +: leftTypes: _*).toList)

        case (_, SumT(rightTypes)) =>
          SumT(Set(other +: rightTypes: _*).toList)

        case _ =>
          if (this == other) this else SumT(List(this, other))
      }
    }
  }

  /**
    * A type variable.
    */
  case class UnknownT() extends CellT

  /**
    * A cell constant, that is, just a name.
    */
  case class ConstT() extends CellT

  /**
    * A Boolean cell type.
    */
  case class BoolT() extends CellT

  /**
    * An integer cell type.
    */
  case class IntT() extends CellT

  /**
    * Sum type T1 + ... + Tn.
    *
    * @deprecated Not used in our semantics anymore, but may reappear in the future.
    */
  case class SumT(components: Seq[CellT]) extends CellT

  /**
    * A finite set.
    *
    * @param elemType the elements type
    */
  case class FinSetT(elemType: CellT) extends CellT

  /**
    * A function type.
    *
    * @param domType    the type of the domain (must be a finite set).
    * @param resultType result type (not co-domain!)
    */
  case class FunT(domType: CellT, resultType: CellT) extends CellT

  /**
    * A tuple type
    *
    * @param args the types of the tuple elements
    */
  case class TupleT(args: Seq[CellT]) extends CellT

  /**
    * A record type
    *
    * @param fields a map of fields and their types
    */
  case class RecordT(fields: Map[String, CellT]) extends CellT


  /**
    * Unify two types decorated with Option.
    *
    * @param left a left type (may be None)
    * @param right a right type (may be None)
    * @return Some(unifier), if there is one, otherwise None
    */
  def unifyOption(left: Option[CellT], right: Option[CellT]): Option[CellT] = {
    (left, right) match {
      case (Some(l), Some(r)) =>
        l.unify(r)

      case _ =>
        None
    }
  }

}
