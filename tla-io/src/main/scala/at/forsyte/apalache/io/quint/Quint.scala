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
import at.forsyte.apalache.tla.lir.TlaDecl
import at.forsyte.apalache.tla.lir.TlaConstDecl
import at.forsyte.apalache.tla.lir.Typed
import at.forsyte.apalache.tla.lir.TlaVarDecl
import at.forsyte.apalache.tla.lir.TypeTag
import at.forsyte.apalache.tla.lir.TlaAssumeDecl
import at.forsyte.apalache.tla.lir.TlaModule

class Quint(moduleData: QuintOutput) {
  protected val module = moduleData.modules(0)
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
  // Since we need access to the statefull uniqeLambdaName, this class must be
  // defined in the Quint class rather than in its companion object (like the toTlaType class)
  private[quint] class exToTla {
    import QuintEx._
    import QuintType._

    // Construct Apalache IR expressions
    val tla = new ScopedBuilder()

    // Derive a OperParam from a paramter name and it's type.
    //
    // OperParams are required by the ScopedBuilder for building
    // operators and consist of the param's name and its arity,
    // which we here derive from the QuintType.
    private val operParam: ((String, QuintType)) => OperParam = {
      case (name, QuintOperT(args, _)) => OperParam(name, args.length)
      case (name, _)                   => OperParam(name, 0) // Otherwise, we have a value
    }

    // QuintLambda is used both for anonymous operators and for defined
    // operators that take parameters, but these require different constructs
    // in Apalache's IR. Thus, we need to decompose the parts of a QuintLambda
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
        (tlaExpression(body), typedParams)
    }

    private val opDefConverter: QuintDef.QuintOpDef => TBuilderOperDeclInstruction = {
      case QuintDef.QuintOpDef(_, name, _, expr, _) =>
        val (body, typedParams) = expr match {
          // Parameterized operators are defined in Quint using Lambdas
          case lam: QuintLambda => lambdaBodyAndParams(lam)
          // Otherwise it's an operator with no params
          case other => (tlaExpression(other), List())
        }
        tla.decl(name, body, typedParams: _*)
    }

    private def typeTagOfId(id: Int): TypeTag = {
      Typed(Quint.typeToTlaType(types(id).typ))
    }

    private[quint] val tlaDef: QuintDef => Option[TlaDecl] = {
      import QuintDef._
      {
        // We don't currently support type definitions in the Apalache IR:
        // all compound types are expected to be inlined.
        case QuintTypeDef(_, _, _) => None
        // Constant and var declarations are trivial to construct, and
        // no methods for them are provided by the ScopedBuilder.
        case QuintConst(id, name, _) => Some(TlaConstDecl(name)(typeTagOfId(id)))
        case QuintVar(id, name, _)   => Some(TlaVarDecl(name)(typeTagOfId(id)))
        case op: QuintOpDef          => Some(build(opDefConverter(op)))
        case QuintAssume(id, _, quintEx) =>
          val tlaEx = build(tlaExpression(quintEx))
          Some(TlaAssumeDecl(tlaEx)(typeTagOfId(id)))
      }
    }

    private type T = TBuilderInstruction

    private def throwOperatorArityError(op: String, arity: String, args: List[QuintEx]) =
      // This should be impossible to hit, unless quint produces a malformed AST
      throw new QuintIRParseError(s"too many arguments passed to ${arity} operator ${op}: ${args}")

    // The following *App operators are helpers to factor out building operator applications
    // and the related error handling for operators of different arities.
    private val unaryApp: (String, T => T) => List[QuintEx] => T =
      (op, tlaBuilder) => {
        case a :: Nil    => tlaBuilder(tlaExpression(a))
        case tooManyArgs => throwOperatorArityError(op, "unary", tooManyArgs)
      }

    private val binaryApp: (String, (T, T) => T) => List[QuintEx] => T =
      (op, tlaBuilder) => {
        case a :: b :: Nil => tlaBuilder(tlaExpression(a), tlaExpression(b))
        case tooManyArgs   => throwOperatorArityError(op, "binary", tooManyArgs)
      }

    private val variadicApp: (Seq[T] => T) => List[QuintEx] => T =
      // opName ignored since we can't hit an arity error
      tlaBuilder => args => tlaBuilder(args.map(tlaExpression))

    private val tlaApplication: QuintApp => TBuilderInstruction = { case QuintApp(id, opName, quintArgs) =>
      val applicationBuilder: List[QuintEx] => TBuilderInstruction = opName match {
        // First we check for application of builtin operators

        // Booleans
        case "eq"      => binaryApp(opName, tla.eql)
        case "neq"     => binaryApp(opName, tla.neql)
        case "iff"     => binaryApp(opName, tla.equiv)
        case "implies" => binaryApp(opName, tla.impl)
        case "not"     => unaryApp(opName, tla.not)
        case "and"     => variadicApp(args => tla.and(args: _*))
        case "or"      => variadicApp(args => tla.or(args: _*))

        // Actions
        case "assign"    => binaryApp(opName, (lhs, rhs) => tla.assign(tla.prime(lhs), rhs))
        case "actionAll" => variadicApp(args => tla.and(args: _*))
        case "actionAny" => variadicApp(args => tla.or(args: _*))

        // Otherwise, the applied operator is defined, and not a builtin
        case definedOpName => { args =>
          val paramTypes = args.map(arg => Quint.typeToTlaType(types(arg.id).typ))
          val returnType = Quint.typeToTlaType(types(id).typ)
          val operType = OperT1(paramTypes, returnType)
          val oper = tla.name(definedOpName, operType)
          val tlaArgs = args.map(tlaExpression)
          tla.appOp(oper, tlaArgs: _*)
        }
      }
      applicationBuilder(quintArgs)
    }

    private val tlaExpression: QuintEx => TBuilderInstruction = {
      case QuintBool(_, b)          => tla.bool(b)
      case QuintInt(_, i)           => tla.int(i)
      case QuintStr(_, s)           => tla.str(s)
      case QuintName(id, n)         => tla.name(n, Quint.typeToTlaType(types(id).typ))
      case QuintLet(_, opDef, expr) => tla.letIn(tlaExpression(expr), opDefConverter(opDef))
      case lam: QuintLambda =>
        val (body, typedParams) = lambdaBodyAndParams(lam)
        tla.lambda(uniqueLambdaName(), body, typedParams: _*)
      case app: QuintApp => tlaApplication(app)
    }

    val convert: QuintEx => Try[TlaEx] = quintEx => Try(build(tlaExpression(quintEx)))
  }

  /**
   * Convert a [[QuintEx]] to a [[TlaEx]]
   */
  private[quint] object exToTla {
    def apply(quintExp: QuintEx): Try[TlaEx] = (new exToTla()).convert(quintExp)
  }

  /**
   * Convert a [[QuintDef]] to a [[TlaDecl]]
   */
  private[quint] object defToTla {
    def apply(quintDef: QuintDef): Try[TlaDecl] =
      (new exToTla())
        .tlaDef(quintDef)
        .toRight(new QuintIRParseError(s"Definition ${quintDef} was not convertible to TLA"))
        .toTry
  }
}

object Quint {

  def apply(readable: ujson.Readable): Try[Quint] = QuintOutput.read(readable).map(new Quint(_))

  def toTla(readable: ujson.Readable): Try[TlaModule] = for {
    quint <- Quint(readable)
    declarations <- Try(quint.module.defs.map(quint.defToTla(_).get))
    name = quint.module.name
  } yield TlaModule(name, declarations)

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
