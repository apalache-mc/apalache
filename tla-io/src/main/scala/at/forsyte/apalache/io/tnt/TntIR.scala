package at.forsyte.apalache.io.tnt

// This package uses upickle'ss macros to generate serialization functions.
// See https://com-lihaoyi.github.io/upickle/#Builtins

// Allows customizing the JSON key for a class tag or attribute
// See https://com-lihaoyi.github.io/upickle/#CustomKeys
import upickle.implicits.key
import scala.util.Try

object TntDeserializer extends upickle.AttributeTagged {

  // By default, upickle uses the key `"$type"` to differentiate cases of a case
  // class, but TNT uses the key `"kind"` to encode the variant tag. This
  // override forms a custom deserializer that is just like the default, except
  // the value of "kind" is used to differentiate
  override def tagName = "kind"

}

import TntDeserializer.{macroRW, ReadWriter => RW}

case class TntModule(
    id: Int,
    name: String,
    defs: List[TntDef])
object TntModule {
  implicit val rw: RW[TntModule] = macroRW
}

class TntIRParseError(errMsg: String) extends Exception("Input was not a valid representation of the TntIR: " + errMsg)

/** The JSON output produced by tntc parse */
case class TntcOutput(module: TntModule)
object TntcOutput {
  implicit val rw: RW[TntcOutput] = macroRW

  def read(s: ujson.Readable): Try[TntcOutput] =
    Try(TntDeserializer.read[TntcOutput](s)).recoverWith { case err: upickle.core.AbortException =>
      scala.util.Failure(new TntIRParseError(err.clue))
    }
}

trait WithID {
  val id: Int

}

sealed trait TntEx extends WithID

object TntEx {

  // TODO
  implicit val rw: RW[TntEx] =
    RW.merge(Name.rw, Bool.rw, TntInt.rw, Str.rw, App.rw, Lambda.rw, Let.rw)

  /** A name of: a variable, constant, parameter, user-defined operator */
  @key("name") case class Name(id: Int, name: String) extends TntEx {}
  object Name {
    implicit val rw: RW[Name] = macroRW
  }

  /** The boolean literal value */
  @key("bool") case class Bool(id: Int, value: Boolean) extends TntEx {}
  object Bool {
    implicit val rw: RW[Bool] = macroRW
  }

  /** The integer literal value */
  @key("int") case class TntInt(id: Int, value: Int) extends TntEx {}
  object TntInt {
    implicit val rw: RW[TntInt] = macroRW
  }

  /** The string literal value */
  @key("str") case class Str(id: Int, value: String) extends TntEx {}
  object Str {
    implicit val rw: RW[Str] = macroRW
  }

  @key("app") case class App(
      id: Int,
      /** The name of the operator being applied */
      opcode: String,
      /** A list of arguments to the operator */
      args: List[TntEx])
      extends TntEx {}
  object App {
    implicit val rw: RW[App] = macroRW
  }

  @key("lambda") case class Lambda(
      id: Int,
      /** Identifiers for the formal parameters */
      params: List[String],
      /** The qualifier for the defined operator */
      // TODO should this be a sumtype?
      qualifier: String,
      /** The definition body */
      expr: TntEx)
      extends TntEx {}
  object Lambda {
    implicit val rw: RW[Lambda] = macroRW
  }

  @key("let") case class Let(
      id: Int,
      /** The operator being defined to be used in the body */
      opdef: TntDef.Def,
      /** The body */
      expr: TntEx)
      extends TntEx {}
  object Let {
    implicit val rw: RW[Let] = macroRW
  }
}

sealed trait TntDef extends WithID

object TntDef {
  implicit val rw: RW[TntDef] = RW.merge(Def.rw, Var.rw, Const.rw, Assume.rw, TypeDef.rw)

  trait WithOptionalTypeAnnotation {
    // TODO need encoding of TNT type
    val typeAnnotation: Option[TntType]
  }

  trait WithTypeAnnotation {
    // TODO need encoding of TNT type
    val typeAnnotation: TntType
  }

  /**
   * A user-defined operator that is defined via one of the qualifiers: val, def, pred, action, or temporal. Note that
   * TntOpDef does not have any formal parameters. If an operator definition has formal parameters, then `expr` should
   * be a lambda expression over those parameters.
   */
  @key("def") case class Def(
      id: Int,
      /** definition name */
      name: String,
      /** definition qualifier: 'val', 'def', 'action', 'temporal' */
      // Should it be a sum type?
      qualifier: String,
      /** expression to be associated with the definition */
      expr: TntEx,
      typeAnnotation: Option[TntType] = None)
      extends TntDef with WithOptionalTypeAnnotation {}
  object Def {
    implicit val rw: RW[Def] = macroRW
  }

  @key("const") case class Const(
      id: Int,
      /** name of the constant */
      name: String,
      typeAnnotation: TntType)
      extends TntDef with WithTypeAnnotation {}
  object Const {
    implicit val rw: RW[Const] = macroRW
  }

  @key("var") case class Var(
      id: Int,
      /** name of the variable */
      name: String,
      typeAnnotation: TntType)
      extends TntDef with WithTypeAnnotation {}
  object Var {
    implicit val rw: RW[Var] = macroRW
  }

  @key("assume") case class Assume(
      id: Int,
      /** name of the assumption, may be '_' */
      name: String,
      /** an expression to associate with the name */
      assumption: TntEx)
      extends TntDef {}
  object Assume {
    implicit val rw: RW[Assume] = macroRW
  }

  /**
   * TntTypeDefs represent both type aliases and abstract types
   *
   *   - Abstract types do not have an associated `type`
   *   - Type aliases always have an associated `type`
   */
  @key("typedef") case class TypeDef(
      id: Int,
      /** name of a type alias */
      name: String,
      /**
       * type to associate with the alias (none for uninterpreted type)
       *
       * Type aliases have `Some(type)` while abstract types have `None`
       */
      // TODO need special instruction for this conversion
      typ: Option[TntType])
      extends TntDef {}
  object TypeDef {
    implicit val rw: RW[TypeDef] = macroRW
  }
}

/**
 * TNT expressions, declarations and types carry a unique identifier, which can be used to recover expression metadata
 * such as source information, annotations, etc.
 */
sealed trait TntType {
  val id: Int
}

object TntType {

  implicit val rw: RW[TntType] = RW.merge(
      TntBoolType.rw,
      TntIntType.rw,
      TntStrType.rw,
      TntConstType.rw,
      TntVarType.rw,
      TntSetType.rw,
      TntSeqType.rw,
      TntFunType.rw,
      TntOperType.rw,
      TntTupleType.rw,
      TntRecordType.rw,
      TntUnionType.rw,
  )

  // NOTE: We default id to -1 in the following because upickle handles optional values stupidly
  // and won't handle Option[Int] in the expected way.

  @key("bool") case class TntBoolType(id: Int = -1) extends TntType {}
  object TntBoolType {
    implicit val rw: RW[TntBoolType] = macroRW
  }

  @key("int") case class TntIntType(id: Int = -1) extends TntType
  object TntIntType {
    implicit val rw: RW[TntIntType] = macroRW
  }

  @key("str") case class TntStrType(id: Int = -1) extends TntType
  object TntStrType {
    implicit val rw: RW[TntStrType] = macroRW
  }

  @key("const") case class TntConstType(id: Int = -1, name: String) extends TntType
  object TntConstType {
    implicit val rw: RW[TntConstType] = macroRW
  }

  @key("var") case class TntVarType(id: Int = -1, name: String) extends TntType
  object TntVarType {
    implicit val rw: RW[TntVarType] = macroRW
  }

  @key("set") case class TntSetType(id: Int = -1, elem: TntType) extends TntType
  object TntSetType {
    implicit val rw: RW[TntSetType] = macroRW
  }

  @key("list") case class TntSeqType(id: Int = -1, elem: TntType) extends TntType
  object TntSeqType {
    implicit val rw: RW[TntSeqType] = macroRW
  }

  @key("fun") case class TntFunType(id: Int = -1, arg: TntType, res: TntType) extends TntType
  object TntFunType {
    implicit val rw: RW[TntFunType] = macroRW
  }

  @key("oper") case class TntOperType(id: Int = -1, args: List[TntType], res: TntType) extends TntType
  object TntOperType {
    implicit val rw: RW[TntOperType] = macroRW
  }

  @key("tup") case class TntTupleType(id: Int = -1, elems: List[TntType]) extends TntType
  object TntTupleType {
    implicit val rw: RW[TntTupleType] = macroRW
  }

  case class TntRecordField(fieldName: String, fieldType: TntType)
  object TntRecordField {
    implicit val rw: RW[TntRecordField] = macroRW
  }

  sealed trait Row

  object Row {
    implicit val rw: RW[Row] = RW.merge(Cell.rw, Var.rw, Nil.rw)

    @key("row") case class Cell(fields: List[TntRecordField], other: Row) extends Row
    object Cell {
      implicit val rw: RW[Cell] = macroRW
    }

    @key("var") case class Var(name: String) extends Row
    object Var {
      implicit val rw: RW[Var] = macroRW
    }

    @key("empty") case class Nil() extends Row
    object Nil {
      implicit val rw: RW[Nil] = macroRW
    }
  }

  @key("rec") case class TntRecordType(id: Int = -1, fields: Row) extends TntType
  object TntRecordType {
    implicit val rw: RW[TntRecordType] = macroRW
  }

  case class UnionRecord(tagValue: String, fields: Row)
  object UnionRecord {
    implicit val rw: RW[UnionRecord] = macroRW
  }

  @key("union") case class TntUnionType(id: Int = -1, tag: String, records: List[UnionRecord]) extends TntType
  object TntUnionType {
    implicit val rw: RW[TntUnionType] = macroRW
  }
}
