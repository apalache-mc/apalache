package at.forsyte.apalache.io.quint

import at.forsyte.apalache.tla.lir.BoolT1
import at.forsyte.apalache.tla.lir.ConstT1
import at.forsyte.apalache.tla.lir.FunT1
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.lir.OperParam
import at.forsyte.apalache.tla.lir.OperT1
import at.forsyte.apalache.tla.lir.RecRowT1
import at.forsyte.apalache.tla.lir.RowT1
import at.forsyte.apalache.tla.lir.SeqT1
import at.forsyte.apalache.tla.lir.SetT1
import at.forsyte.apalache.tla.lir.StrT1
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.TlaType1
import at.forsyte.apalache.tla.lir.TupT1
import at.forsyte.apalache.tla.lir.VarT1
import at.forsyte.apalache.tla.lir.VariantT1
import at.forsyte.apalache.tla.typecomp.ScopedBuilder
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.typecomp.TBuilderOperDeclInstruction
import at.forsyte.apalache.tla.typecomp.build
import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable
import scala.util.Try

class Quint(moduleData: QuintOutput) {
  private val types = moduleData.types

  // benign state to generate unique names for lambdas
  private var uniqueLambdaNo = 0
  private def uniqueLambdaName(): String = {
    val n = uniqueLambdaNo
    uniqueLambdaNo += 1
    s"__QUINT_LAMBDA${n}"
  }

  // Convert a QuintEx into a TlaEx
  //
  // We implement a small family of mutually recursive conversion functions using this
  // class in order to:
  //
  // - Encapsulate and store benign state used by the ScopedBuilder (see below)
  // - Support and encapsulate the mutual recursion needed in the methods
  //
  // Since we need access to the statefull uniqeLambdaName state, this class must be
  // defined in the Quint class rather than in its companion object (like the toTlaType class)
  private[quint] class exToTla {
    import QuintEx._
    import QuintType._

    // Construct Apalache IR expressions
    val exp = new ScopedBuilder()

    // QuintLambda is used both for anonymous operators and for defined
    // operators that take parameters, but these require different constructs
    // in Apalache's IR. Thus, we need to decompose the parts of a QuintLamba
    // for two different purposes.
    private val lambdaBodyAndParams: QuintLambda => (TBuilderInstruction, List[(OperParam, TlaType1)]) = {
      case ex @ QuintLambda(id, paramNames, _, body) =>
        val quintParamTypes = types(id).typ match {
          case QuintOperT(types, _) => types
          case invalidType          => throw new QuintIRParseError(s"lambda ${ex} has invalid type ${invalidType}")
        }
        val operParams = paramNames.zip(quintParamTypes).map(operParam)
        val paramTypes = quintParamTypes.map(Quint.typeToTlaType(_))
        val typedParams = operParams.zip(paramTypes)
        (expConverter(body), typedParams)
    }

    private val defConverter: QuintDef => TBuilderOperDeclInstruction = {
      import QuintDef._

      {
        case QuintOpDef(_, name, _, expr, _) =>
          val (body, typedParams) = expr match {
            // Parameterized operators are defined in Quint using Lambdas
            case lam: QuintLambda => lambdaBodyAndParams(lam)
            // Otherwise it's an operator with no params
            case other => (expConverter(other), List())
          }
          exp.decl(name, body, typedParams: _*)
        // TODO
        case QuintConst(_, _, _)   => null
        case QuintVar(_, _, _)     => null
        case QuintAssume(_, _, _)  => null
        case QuintTypeDef(_, _, _) => null
      }
    }

    // Derive a OperParam from a paramter
    // name and it's type
    private val operParam: ((String, QuintType)) => OperParam = {
      case (name, QuintOperT(args, _)) => OperParam(name, args.length)
      case (name, _)                   => OperParam(name, 0) // Otherwise, we have a value
    }

    private val expConverter: QuintEx => TBuilderInstruction = {
      case QuintBool(_, b)          => exp.bool(b)
      case QuintInt(_, i)           => exp.int(i)
      case QuintStr(_, s)           => exp.str(s)
      case QuintName(id, n)         => exp.name(n, Quint.typeToTlaType(types(id).typ))
      case QuintLet(_, opdef, expr) => exp.letIn(expConverter(expr), defConverter(opdef))
      case lam: QuintLambda =>
        val (body, typedParams) = lambdaBodyAndParams(lam)
        exp.lambda(uniqueLambdaName(), body, typedParams: _*)
      case QuintApp(id, op, quintArgs) =>
        val operType = Quint.typeToTlaType(types(id).typ)
        val oper = exp.name(op, operType)
        val args = quintArgs.map(expConverter)
        exp.appOp(oper, args: _*)
    }

    val convert: QuintEx => Try[TlaEx] = exp => Try(build(expConverter(exp)))
  }

  /**
   * Convert a [[QuintEx]] to a [[TlaEx]]
   */
  private[quint] object exToTla {
    def apply(quintExp: QuintEx): Try[TlaEx] = (new exToTla()).convert(quintExp)
  }
}

object Quint {

  // Convert a QuintType into a TlaType1
  //
  // We implement a small family of mutually recursive conversion functions using this
  // class in order to:
  //
  // - Encapsulate and store benign state used to track variable numbers (see below)
  // - Support and encapsulate the mutual recursion needed in the methods
  private[quint] class typeToTlaType() extends LazyLogging {

    // quint type variables are represented with strings, but in TlaType1 they are integers.
    // This little bundle of state lets us track the conversion of quint var names to
    // TlaType1 var numbers.
    //
    // Since the scope of type variables in quint is always limited to single top-level type expressions,
    // and since the converter class is constructed fresh for each (top-level) type conversion,
    // we don't need to worry about variable name collisions.
    var varNo = 0
    val vars = mutable.Map[String, Int]()
    def getVarNo(varName: String): Int = {
      vars.get(varName) match {
        case None    => val v = varNo; varNo += 1; v
        case Some(n) => n
      }
    }

    import QuintType._

    def rowToTupleElems(row: Row): List[TlaType1] = {
      // Since we have to concat lists here, which can be expensive, we use an
      // accumulator to benefit from tail call optimization. This is purely a precaution.
      def aux(r: Row, acc0: List[TlaType1]): List[TlaType1] = r match {
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

    def rowToRowT1(row: Row): RowT1 = {

      // `aux(r, acc)` is a `(fields, other)`
      // where `fields` is the list of field names and their types, and
      // `other` is either `Some(var)` for an open row or `None` for a closed row.
      //
      // `acc` is used as an accumulator to enable tail recursion
      def aux(r: Row, acc0: List[(String, TlaType1)]): (List[(String, TlaType1)], Option[VarT1]) = r match {
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
    def unionToRowT1(variants: List[UnionRecord]): RowT1 = {
      val fieldTypes = variants.map {
        case UnionRecord(tag, row) => {
          (tag, RecRowT1(rowToRowT1(row)))
        }
      }
      RowT1(fieldTypes: _*)
    }

    val convert: QuintType => TlaType1 = {
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
   * Convert a [[QuintType]] to a [[TlaType1]]
   */
  private[quint] object typeToTlaType {
    def apply(quintType: QuintType): TlaType1 = new typeToTlaType().convert(quintType)
  }
}
