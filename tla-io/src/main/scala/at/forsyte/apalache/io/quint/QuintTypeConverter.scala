package at.forsyte.apalache.io.quint

import at.forsyte.apalache.tla.lir._
import com.typesafe.scalalogging.LazyLogging

import scala.collection.immutable.SortedMap
import scala.collection.mutable

// Convert a QuintType into a TlaType1
//
// We implement a small family of mutually recursive conversion functions using this
// class in order to:
//
// - Encapsulate and store benign state used to track variable numbers (see below)
// - Support and encapsulate the mutual recursion needed in the methods
private class QuintTypeConverter extends LazyLogging {

  // quint type variables are represented with strings, but in TlaType1 they are integers.
  // This little bundle of state lets us track the conversion of quint var names to
  // TlaType1 var numbers.
  //
  // Since the scope of type variables in quint is always limited to single top-level type expressions,
  // and since the converter class is constructed fresh for each (top-level) type conversion,
  // we don't need to worry about variable name collisions.
  private var varNo = 0
  private val vars = mutable.Map[String, Int]()
  private def getVarNo(varName: String): Int = {
    vars.get(varName) match {
      case None =>
        val v = varNo
        vars += varName -> v
        varNo += 1
        v
      case Some(n) => n
    }
  }

  import QuintType._

  private def rowToTupleT1(row: Row): TlaType1 = {
    // `aux(r, acc)` is a `(fields, other)`
    // where `fields` is a map from tuple indices to tuple types, and
    // `other` is either `Some(var)` for an open row or `None` for a closed row.
    //
    // `acc` is used as an accumulator to enable tail recursion
    def aux(r: Row, acc0: SortedMap[Int, TlaType1]): (SortedMap[Int, TlaType1], Option[VarT1]) = r match {
      case Row.Nil()  => (acc0, None)
      case Row.Var(v) => (acc0, Some(VarT1(getVarNo(v))))
      case Row.Cell(fields, other) =>
        val acc1 = acc0 ++ fields.map { f => (f.fieldName.toInt + 1) -> convert(f.fieldType) }
        aux(other, acc1)
    }

    aux(row, SortedMap()) match {
      case (fields, None)    => TupT1(fields.map(_._2).toSeq: _*)
      case (fields, Some(_)) => SparseTupT1(fields)
    }
  }

  private def rowToRowT1(row: Row): RowT1 = {

    // `aux(r, acc)` is a `(fields, other)`
    // where `fields` is the list of field names and their types, and
    // `other` is either `Some(var)` for an open row or `None` for a closed row.
    //
    // `acc` is used as an accumulator to enable tail recursion
    def aux(r: Row, acc0: Seq[(String, TlaType1)]): (Seq[(String, TlaType1)], Option[VarT1]) = r match {
      case Row.Nil()  => (acc0, None)
      case Row.Var(v) => (acc0, Some(VarT1(getVarNo(v))))
      case Row.Cell(fields, other) =>
        val acc1 = fields.map { case f => (f.fieldName, convert(f.fieldType)) } ++ acc0
        aux(other, acc1)
    }

    aux(row, List()) match {
      case (fields, None)          => RowT1(fields: _*)
      case (fields, Some(typeVar)) => RowT1(typeVar, fields: _*)
    }
  }

  val convert: QuintType => TlaType1 = {
    case QuintBoolT() => BoolT1
    case QuintIntT()  => IntT1
    case QuintStrT()  => StrT1
    case QuintConstT(name) =>
      ConstT1(name) // TODO: Raise error if we hit this. See https://github.com/informalsystems/apalache/issues/2788
    case QuintVarT(name)       => VarT1(getVarNo(name))
    case QuintSetT(elem)       => SetT1(convert(elem))
    case QuintSeqT(elem)       => SeqT1(convert(elem))
    case QuintFunT(arg, res)   => FunT1(convert(arg), convert(res))
    case QuintOperT(args, res) => OperT1(args.map(convert), convert(res))
    case QuintTupleT(Row.Nil()) =>
      ConstT1("UNIT") // Use the Unit type for empty tuples, since they are the unit type in Quint
    case QuintTupleT(row)  => rowToTupleT1(row)
    case QuintRecordT(row) => RecRowT1(rowToRowT1(row))
    case QuintSumT(row)    => VariantT1(rowToRowT1(row))
  }
}
