package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper, TlaFunOper, TlaOper}

// We use shapeless for facilitating the type-level encodings of TlaExpressions
import shapeless._
import poly._

// A (very) rough sketch at what TLA Expressions might look like when
// we represent out typing discipline inside of Scala's type system.
object Tla {
  // The type of any TLA expression
  sealed trait Exp[T] {
    def toString: String
  }

  // Just an alias
  type IntT = BigInt

  // A value constructs a TLA expression tagged with the Scala type it carries as a payload.
  class Value[T](value: T) extends Exp[T]
  case class Int(value: IntT) extends Value(value)
  case class Str(value: String) extends Value(value)
  case class Bool(value: Boolean) extends Value(value)

  // Each compound expression is reprsented by a new type

  sealed trait SeqType[T]
  case class TlaSeq[T](seq: Seq[Exp[T]]) extends Exp[SeqType[T]]

  sealed trait TupleType[A, B]
  case class Empty() extends Exp[TupleType[Unit, Unit]]
  case class Single[A](fst: A) extends Exp[TupleType[A, Unit]]
  case class Tuple[A, B](fst: A, snd:B) extends Exp[TupleType[A, B]]

  sealed trait RecType[Fields]
  case class Rec[Fields <: HList](fields: Fields) extends Exp[RecType[Fields]]

  sealed trait OperType[Args <: HList, Ret]

  // Names are expressions
  // The idea here is that names also record the type of the expression
  // they refer to. When we don't know what that type is, we might use
  // `Name[Exp[Any]]`.
  case class Name[T](name: String) extends Exp[T]

  // An unapplied operator
  case class Op[Args <: HList, Ret](oper: TlaOper)
      extends Exp[OperType[Args, Ret]]

  // Application of an operator
  case class App[Args <: HList, Ret](op: Exp[OperType[Args, Ret]], args: Args)
      extends Exp[Ret]

  // Binary operators of type (T, T) => Ret
  type BinOpApp[T, Ret] = App[T :: T :: HNil, Ret]
  type Tup[A, B] = Exp[TupleType[A, B]]
}

// Utility functions for constructing expressions. Most of these don't actually do much,
// but a few are useful.
object TypeLevelBuilder {
  import Tla._

  def binOp[T, Ret](op: TlaOper)(a: T, b: T): Exp[Ret] = App(Op(op), a :: b :: HNil)

  def plus: (Exp[IntT], Exp[IntT]) => Exp[Tla.IntT] =
    binOp(TlaArithOper.plus)

  // A polymorphic operator
  def equal[T]: (Exp[T], Exp[T]) => Exp[Boolean] =
    binOp(TlaOper.eq)

  def and(a: Exp[Boolean], b: Exp[Boolean]): Exp[Boolean] =
    binOp(TlaBoolOper.and)(a, b)

  // Variadic conjunction
  def and(args: Exp[Boolean]*): Exp[Boolean] = args match {
    case Seq() => Bool(true)
    case arg +: args => and(arg, and(args: _*))
  }

  // Polymorphic sequences
  // def seq[T](): Seq[T] = Nil()
  // def seq[T](args: Exp[T]*): Seq[T] = args match {
  //   case Seq() => Nil()
  //   case arg +: args => Cons(arg, seq(args: _*))
  // }

  def seq[T](args: Exp[T]*): TlaSeq[T] = {
    TlaSeq(args)
  }

  // def tup[A, B](a: A, b: B): A => B => Tup[A, B] = a => b => Tuple(a, b)
  def tup[A, B](a: A, b: B): Tup[A, B] = {
    Tuple(a, b)
  }
}

// These examples illustrate construction of expressions, and, commented out,
// constructions which are impossible at compile time, due to invalid construction
object Example {
  import TypeLevelBuilder._

  // Atomic values
  val exInt: Tla.Int = Tla.Int(1)
  val exStr: Tla.Str = Tla.Str("foo")
  val exFalse: Tla.Bool = Tla.Bool(false)
  val exTrue: Tla.Bool = Tla.Bool(true)

  val exPlus = plus(exInt, exInt)

  // NOTE: Statically fails with type error
  // val exInvalidPlus = plus(exInt, exStr)
  // Will statically fail with:
  // [E]      type mismatch;
  // [E]       found   : at.forsyte.apalache.tla.lir.TypeLevelTlaEx.Tla.Str
  // [E]       required: at.forsyte.apalache.tla.lir.TypeLevelTlaEx.Tla.Int
  // [E]      L116:     val exBadPlus = Builder.plus(exInt, exStr)
  // [E]                                                    ^^^^^

  // Emonstration of polymorphic use of `equal`
  val exIntEquals = equal(exInt, exInt)
  val exStrEquals = equal(exStr, exStr)

  // NOTE: Statically fails with type error
  // val exInvalidEquals = equal(exStr, exInt)

  val exBinaryAnd = and(exIntEquals, exStrEquals)
  val exVariadicAnd = and(exBinaryAnd, Tla.Bool(true), Tla.Bool(false), Tla.Bool(false))

  // NOTE: Statically fails with type error
  // val exInvalidAnd = and(exInt, Tla.Bool(true))

  val exIntSeq = seq(Tla.Int(1), Tla.Int(2), Tla.Int(3))
  val exStrSeq = seq(Tla.Str("one"), Tla.Str("two"), Tla.Str("three"))

  // Type inference will give us differently typed empty seqs
  val exEmptyIntSeq: Tla.TlaSeq[Tla.IntT] = seq()
  val exEmptyStrSeq: Tla.TlaSeq[Tla.Str] = seq()
  val exEmptyBoolSeq = seq[Tla.Bool]()

  // NOTE: Statically fails with type error
  // val exInvalidSeq = seq(Tla.Str("one"), Tla.Int(2))

  val exTuple: Tla.Tup[Tla.Int, Tla.Str] = tup(exInt, exStr)
  val exNestedTuple = tup(exTrue, exTuple)
  val exTupleOfSeq = tup(seq(Tla.Int(1), Tla.Int(2)), exStr)
  val exSeqOfTuple = seq(tup(exInt, exStr), tup(Tla.Int(1), Tla.Str("bar")))

  // NOTE: Statically fails with type error, due to clash with annotation
  // val exInvalidTuple: Tla.Tup[Tla.Str, Tla.Str] = tup(Tla.Str("one"), Tla.Int(2))
  // NOTE: Statically fails with type error, due to incompatible tuples
  // val exInvalidSeqOfTuple = seq(tup(exInt, exStr), tup(exStr, exInt))

  // We need some extra machinery for records, but Shapeless supports type-level key-value
  // encoding
  import shapeless._
  import record._
  import syntax.singleton._

  val exRecord = Tla.Rec(("msg" ->> Tla.Str("hello")) :: ("value" ->> Tla.Int(3)) :: HNil)
  val exRecordAccess1 = plus(exRecord.fields("value"), Tla.Int(3))
  val exRecordAccess2 = equal(Tla.Str("hello"), exRecord.fields("msg"))

  // NOTE: Statically fails with type error, due to invalid record field type
  // I.e., field "msg" holds a string, so we cannot use it's value in `plus`.
  // val exInvalidRecordAccess = plus(exRecord.fields("msg"), Tla.Int(3))

  def exDynamicConstructionOfRecord() {
    val k1 = readLine()
    val v1 = readInt()

    val k2 = readLine()
    val v2 = readBoolean()

    val rec = Tla.Rec((k1 ->> Tla.Int(v1)) :: (k2 ->> Tla.Bool(v2)) :: HNil)
    val exDynamicPlus = plus(exInt, rec.fields(k1))

    // NOTE: Statically fails with type error, due to invalid record field type
    // val exInvalidDynamicPlus = plus(exInt, rec.fields(k2))
  }

  // Untyped terms
  val exUntypedEmptySeq: Tla.TlaSeq[Any] = seq[Any]()
}
