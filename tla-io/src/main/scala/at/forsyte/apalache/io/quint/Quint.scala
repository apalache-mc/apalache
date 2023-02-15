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

    private val unaryApp: (String, T => T) => List[QuintEx] => T =
      (op, builder) => {
        case a :: Nil    => builder(tlaExpression(a))
        case tooManyArgs => throwOperatorArityError(op, "unary", tooManyArgs)
      }

    private val binaryApp: (String, (T, T) => T) => List[QuintEx] => T =
      (op, builder) => {
        case a :: b :: Nil => builder(tlaExpression(a), tlaExpression(b))
        case tooManyArgs   => throwOperatorArityError(op, "binary", tooManyArgs)
      }

    private val ternaryApp: (String, (T, T, T) => T) => List[QuintEx] => T =
      (op, builder) => {
        case a :: b :: c :: Nil => builder(tlaExpression(a), tlaExpression(b), tlaExpression(c))
        case tooManyArgs        => throwOperatorArityError(op, "ternary", tooManyArgs)
      }

    private val tlaApplication: QuintApp => TBuilderInstruction = { case QuintApp(id, opName, quintArgs) =>
      val applicationBuilder: List[QuintEx] => TBuilderInstruction = opName match {
        // TODO: The builtin quint operators are in the same order as they appear in https://github.com/informalsystems/quint/main/quint/src/builtin.qnt
        case "eq"        => binaryApp(opName, tla.eql)
        case "neq"       => binaryApp(opName, tla.neql)
        case "iff"       => binaryApp(opName, tla.equiv)
        case "implies"   => binaryApp(opName, tla.impl)
        case "not"       => unaryApp(opName, tla.not)
        case "in"        => binaryApp(opName, tla.in)
        case "notin"     => binaryApp(opName, tla.notin)
        case "contains"  => binaryApp(opName, (set, elem) => tla.in(elem, set))
        case "union"     => binaryApp(opName, tla.cup)
        case "intersect" => binaryApp(opName, tla.cap)
        case "exclude"   => binaryApp(opName, tla.setminus)
        case "fold"      => ternaryApp(opName, (set, init, op) => tla.foldSet(op, init, set))
        case "powerset"  => unaryApp(opName, tla.powSet)
        case "flatten"   => unaryApp(opName, tla.union)
        case "allLists"  => unaryApp(opName, tla.seqSet)
        case "oneOf"     => unaryApp(opName, tla.guess)
        case "isFinite"  => unaryApp(opName, tla.isFiniteSet)
        case "size"      => unaryApp(opName, tla.cardinality)
        case "get"       => binaryApp(opName, tla.app)
        case "set"       => ternaryApp(opName, tla.except)
        case "keys"      => unaryApp(opName, tla.dom)
        case "setOfMaps" => binaryApp(opName, tla.funSet)
        case "setToMap"  => unaryApp(opName, tla.setAsFun)
        case "append"    => binaryApp(opName, tla.append)
        case "concat"    => binaryApp(opName, tla.concat)
        case "head"      => unaryApp(opName, tla.head)
        case "tail"      => unaryApp(opName, tla.tail)
        case "length"    => unaryApp(opName, tla.len)
        case "foldl"     => ternaryApp(opName, (seq, init, op) => tla.foldSeq(op, init, seq))

        case "iadd"    => binaryApp(opName, tla.plus)
        case "isub"    => binaryApp(opName, tla.minus)
        case "imul"    => binaryApp(opName, tla.mult)
        case "idiv"    => binaryApp(opName, tla.div)
        case "imod"    => binaryApp(opName, tla.mod)
        case "ipow"    => binaryApp(opName, tla.exp)
        case "ilt"     => binaryApp(opName, tla.lt)
        case "igt"     => binaryApp(opName, tla.gt)
        case "ilte"    => binaryApp(opName, tla.le)
        case "igte"    => binaryApp(opName, tla.ge)
        case "iuminus" => unaryApp(opName, tla.uminus)
        case "to"      => binaryApp(opName, tla.dotdot)

        case "always"     => unaryApp(opName, tla.box)
        case "eventually" => unaryApp(opName, tla.diamond)

        // Action operators
        case "next"       => unaryApp(opName, tla.prime)
        case "orKeep"     => binaryApp(opName, tla.stutt)
        case "mustChange" => binaryApp(opName, tla.nostutt)
        case "enabled"    => unaryApp(opName, tla.enabled)
        case "weakFair"   => binaryApp(opName, (A, e) => tla.WF(e, A))
        case "strongFair" => binaryApp(opName, (A, e) => tla.SF(e, A))
        case "assign"     => binaryApp(opName, tla.assign)
        case "ite"        => ternaryApp(opName, tla.ite)
        case "then"       => binaryApp(opName, tla.comp)
        case "fail"       => unaryApp(opName, tla.not)
        case "assert"     => unaryApp(opName, tla.and(_, tla.bool(true))) // Better way to do this?
        // TODO compound value constructors

        // TODO: Lists indexing requires indexes adjustment, since they are base 0 in quint but base 1 in TLA
        case "nth"       => binaryApp(opName, tla.app)
        case "indices"   => unaryApp(opName, tla.dom)
        case "replaceAt" => ternaryApp(opName, tla.except)
        // TODO: start must be reduced but end left the same (cause it is exclusive in quint)
        case "slice" => ternaryApp(opName, tla.subseq)

        // TODO: These operators require extracting the variable name and exp body from the lambda arg
        case "filter"     => null
        case "map"        => null // filter(S, x => e) ~> tla.map((x => e)(fv), fv \in S')
        case "forall"     => null
        case "chooseSome" => null

        // TODO: need custom constructions?
        case "mapBy"    => null
        case "setBy"    => null
        case "put"      => null
        case "select"   => null
        case "foldr"    => null
        case "repeated" => null
        case "range"    => null

        // The applied operator is defined, and not a builtin
        case definedOpName => { args =>
          val paramTypes = quintArgs.map(arg => Quint.typeToTlaType(types(arg.id).typ))
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
