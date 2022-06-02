package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values._

import scala.collection.immutable.SortedMap

/**
 * Common pseudo-supertype of function, record, sequence and tuple types.
 *
 * Several types in TT1 describe objects with the same kind of functionality: application. Instead of case-splitting in
 * matching, we can simply view each type, for which this is the case, as a pair of two values: {{{(fromT,toT)}}}
 * [Applicative], describing the required argument type and the type of the object after application respectively. For
 * records and tuples, we additionally take an index hint as an argument, because the codomain type may depend on the
 * argument.
 *
 * Note that this abstraction only works when observing an application/update site: <<1,2>>[1] doesn't know or care
 * about any index besides 1, so the tuple types in <<1,2>>[1] and <<1,2,3,4,5>>[1] are both seen as
 * Applicative(Int,Int), despite <<Int, Int>> and <<Int,Int,Int,Int,Int>> being incomparable types. The same is true for
 * EXCEPT-updates.
 *
 * @author
 *   Jure Kukovec
 */
sealed case class Applicative(fromT: TlaType1, toT: TlaType1)

object Applicative {

  /** Returns the domain element type of an Applicative candidate TT1 type, if possible */
  def domainElemType(tt1: TlaType1): Option[TlaType1] = tt1 match {
    case FunT1(domT, _) => Some(domT)
    case _: RecT1       => Some(StrT1)
    case _: RowT1       => Some(StrT1)
    case _: RecRowT1    => Some(StrT1)
    case _: SeqT1       => Some(IntT1)
    case _: SparseTupT1 => Some(IntT1)
    case _: TupT1       => Some(IntT1)
    case _              => None
  }

  private def fromFieldTypes(fieldTypes: SortedMap[String, TlaType1], argHint: TlaEx): Option[Applicative] =
    argHint match {
      case ValEx(TlaStr(s)) => Some(Applicative(StrT1, fieldTypes(s)))
      case _                => None
    }

  /** Represents a TT1 type as Applicative, if possible */
  def asInstanceOfApplicative(tt1: TlaType1, argHint: TlaEx): Option[Applicative] = tt1 match {
    // A function T1 -> T2 application takes a T1 argument and returns a T2 value
    case FunT1(domT, cdmT) => Some(Applicative(domT, cdmT))
    // A record [ s2: T1, s2: T2, ... ] application takes a Str argument and returns
    // a value of type Ti, which depends on the argument value (not just type)
    case RecT1(fieldTypes)              => fromFieldTypes(fieldTypes, argHint)
    case RowT1(fieldTypes, _)           => fromFieldTypes(fieldTypes, argHint)
    case RecRowT1(RowT1(fieldTypes, _)) => fromFieldTypes(fieldTypes, argHint)
    // A sequence Seq(T) application takes an Int argument and returns a T value
    case SeqT1(t) => Some(Applicative(IntT1, t))
    // Sparse tuples are similar to records
    case SparseTupT1(indexTypes) =>
      argHint match {
        case ValEx(TlaInt(i)) => Some(Applicative(IntT1, indexTypes(i.toInt)))
        case _                => None
      }
    // Tuples are similar to records
    case TupT1(tupArgs @ _*) =>
      argHint match {
        case ValEx(TlaInt(i)) =>
          val j = (i - 1).toInt // TLA is 1-indexed, indexedSeq is 0-indexed
          Some(Applicative(IntT1, tupArgs.toIndexedSeq(j)))
        case _ => None
      }
    case _ => None
  }
}
