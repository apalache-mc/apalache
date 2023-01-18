package at.forsyte.apalache.tla.typecomp.signatures

import at.forsyte.apalache.tla.lir.{RecRowT1, RecT1, RowT1, TlaType1}

import scala.collection.immutable.SortedMap

/**
 * Determines flexible equality ([[compatible]]), i.e. an equivalence relation over TT1, which is equality for
 * non-record types, but allows the comparison of records types with compatible fields
 *
 * @author
 *   Jure Kukovec
 */
object FlexibleEquality {

  // None if no common supertype, Some(e) if compatible, and common supertype is e.
  def commonSupertype(lhs: TlaType1, rhs: TlaType1): Option[TlaType1] = (lhs, rhs) match {
    case (a, b) if a == b => Some(a)
    case (RecT1(lFields), RecT1(rFields)) =>
      val intersect = lFields.keySet.intersect(rFields.keySet)
      val intersectMapOpt = intersect.foldLeft(Option(SortedMap.empty[String, TlaType1])) { case (mapOpt, e) =>
        for {
          map <- mapOpt
          supertype <- commonSupertype(lFields(e), rFields(e))
        } yield map + (e -> supertype)
      }
      intersectMapOpt.map { m =>
        RecT1(
            (lFields ++ rFields) ++ m // ++ m last overrides the entries for all e \in intersect with the computed unions
        )
      }
    case (l: RecRowT1, r: RecT1)                       => commonSupertype(r, l)
    case (l: RecT1, RecRowT1(RowT1(fieldTypes, None))) => commonSupertype(l, RecT1(fieldTypes))
    case (RecRowT1(RowT1(lFieldTypes, None)), RecRowT1(RowT1(rFieldTypes, None))) =>
      commonSupertype(RecT1(lFieldTypes), RecT1(rFieldTypes))
    case _ => None
  }

  def commonSeqSupertype(seq: Seq[TlaType1]): Option[TlaType1] =
    seq.headOption.flatMap { h =>
      seq.foldLeft(Option(h)) { case (tOpt, elem) =>
        for {
          t <- tOpt
          superT <- commonSupertype(t, elem)
        } yield superT
      }
    }

  def compatible(lhs: TlaType1, rhs: TlaType1): Boolean = commonSupertype(lhs, rhs).nonEmpty
}
