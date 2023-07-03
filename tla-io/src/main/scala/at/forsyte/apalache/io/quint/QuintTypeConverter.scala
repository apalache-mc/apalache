package at.forsyte.apalache.io.quint

import at.forsyte.apalache.tla.lir._
import com.typesafe.scalalogging.LazyLogging

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

  private def rowToTupleElems(row: Row): Seq[TlaType1] = {
    // Since we have to concat lists here, which can be expensive, we use an
    // accumulator to benefit from tail call optimization. This is purely a precaution.
    def aux(r: Row, acc0: Seq[TlaType1]): Seq[TlaType1] = r match {
      // TODO Update with support for row-based tuples: https://github.com/informalsystems/apalache/issues/1591
      // Row variables in tuples are not currently supported. But we will proceed assuming that this is an
      // over generalization, and that we can safely treat the tuple as a closed tuple type.
      case Row.Var(_) =>
        logger.debug(
            s"Found open row variable in quint tuple with fields $row. Polymorphic tuples are not supported, but we will proceed assuming the tuple can be treated as a closed type.")
        acc0
      case Row.Nil() => acc0
      case Row.Cell(fields, other) =>
        val acc1 = fields.map(f => convert(f.fieldType)) ++ acc0
        aux(other, acc1)
    }

    aux(row, List())
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

  // Convert a quint union to a TlaType1 row (which is used to represent variants)
  //
  // NOTE: Union types in quint aren't fully implemented and supported, so this
  // corner of the transformation is likely to require update soon.
  // See https://github.com/informalsystems/quint/issues/244
  //
  // In quint, unions are currently represented by a list of tagged rows.
  // E.g., (abstracting rom the concrete type representation):
  //
  // ```
  // type u =
  //   | ( "Foo", {a: Int, b: String })
  //   | ( "Bar", {c: Set[Int] })
  // ```
  //
  // But Variant types in Apalache are represented by a single row, in which
  // the row's keys are the tags, and it's values can be of any type, e.g.:
  //
  // ```
  // type u = { "Foo": { a: Int, b: Str }
  //          , "Bar": Set[Int]
  //          }
  // ```
  //
  // Which we parse and represent as
  //
  // ```
  // @typeAlias: u = Foo({a: Int, b: Str}) | Bar(Int);
  // ```
  //
  // As a result, our conversion from quint has to take a list of records of quint
  // rows and convert them into a single TlaType1 record, for which all the values
  // are themselves records, and the keys are given by the values of the `tag`
  // field from quint rows.
  private def unionToRowT1(variants: Seq[UnionRecord]): RowT1 = {
    val fieldTypes = variants.map {
      case UnionRecord(tag, row) => {
        (tag, RecRowT1(rowToRowT1(row)))
      }
    }
    RowT1(fieldTypes: _*)
  }

  private val convert: QuintType => TlaType1 = {
    case QuintBoolT()             => BoolT1
    case QuintIntT()              => IntT1
    case QuintStrT()              => StrT1
    case QuintConstT(name)        => ConstT1(name)
    case QuintVarT(name)          => VarT1(getVarNo(name))
    case QuintSetT(elem)          => SetT1(convert(elem))
    case QuintSeqT(elem)          => SeqT1(convert(elem))
    case QuintFunT(arg, res)      => FunT1(convert(arg), convert(res))
    case QuintOperT(args, res)    => OperT1(args.map(convert), convert(res))
    case QuintTupleT(row)         => TupT1(rowToTupleElems(row): _*)
    case QuintRecordT(row)        => RecRowT1(rowToRowT1(row))
    case QuintUnionT(_, variants) => VariantT1(unionToRowT1(variants))
  }
}

/**
 * Convert a QuintType to a TlaType1.
 *
 * Constructs a fresh scope for translating Quint type variables to Apalache type variables (see
 * QuintTypeConverter.getVarNo() for details).
 */
object QuintTypeConverter {
  def apply(quintType: QuintType): TlaType1 = new QuintTypeConverter().convert(quintType)
}
