package org.apalache_mc.tla.jir.impl

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.ParamUtil
import at.forsyte.apalache.tla.typecomp.{
  ScopeUnsafeBuilder, ScopedBuilder, TBuilderInstruction, TBuilderOperDeclInstruction, TBuilderScopeException,
  TBuilderTypeException,
}
import org.apalache_mc.tla.jir.{
  ExceptUpdate, ExpressionPair, IndexedType, NamedExpression, NamedType, TlaBuilderDecl, TlaBuilderException,
  TlaBuilderExpr, TlaBuilderScopeException, TlaBuilderTypeException, TypedParameter,
}

import java.util.function.Function
import scala.collection.immutable.SortedMap

/**
 * Implementation conversions used by the Java facade.
 *
 * API users should use the builders and factories in `org.apalache_mc.tla.jir`; this object is not a stable API.
 */
object JavaToScalaAdapter {
  /** Converts a Java arbitrary-precision integer to its Scala counterpart. */
  def bigInt(value: java.math.BigInteger): BigInt = BigInt(value)

  /** Maps errors from the underlying builder to the Java facade's exception hierarchy. */
  def translateException(exception: Exception): RuntimeException = exception match {
    case cause: TBuilderTypeException  => new TlaBuilderTypeException(cause.getMessage, cause)
    case cause: TBuilderScopeException => new TlaBuilderScopeException(cause.getMessage, cause)
    case cause: RuntimeException       => cause
    case cause                         => new TlaBuilderException(cause.getMessage, cause)
  }

  /** Creates checked builder state for an integer literal. */
  def checkedInteger(builder: ScopedBuilder, value: BigInt): TBuilderInstruction = builder.int(value)

  /** Creates a scope-unchecked integer literal. */
  def uncheckedInteger(builder: ScopeUnsafeBuilder, value: BigInt): TlaEx = builder.int(value)

  /** Creates checked builder state for a constant literal. */
  def checkedConstant(builder: ScopedBuilder, root: String, constType: ConstT1): TBuilderInstruction =
    builder.const(root, constType)

  /** Creates a scope-unchecked constant literal. */
  def uncheckedConstant(builder: ScopeUnsafeBuilder, root: String, constType: ConstT1): TlaEx =
    builder.const(root, constType)

  /** Unwraps checked expression state. */
  def checkedState(state: Object): TBuilderInstruction =
    state.asInstanceOf[TBuilderInstruction]

  /** Unwraps checked declaration state. */
  def checkedDeclState(state: Object): TBuilderOperDeclInstruction =
    state.asInstanceOf[TBuilderOperDeclInstruction]

  /** Converts pending-expression handles to the underlying builder instructions. */
  def checkedExpressions(
      values: Array[TlaBuilderExpr],
      stateOf: Function[TlaBuilderExpr, Object]): Seq[TBuilderInstruction] =
    values.toIndexedSeq.map(value => checkedState(stateOf.apply(value)))

  /** Converts scope-unchecked expressions to a Scala sequence. */
  def uncheckedExpressions(values: Array[TlaEx]): Seq[TlaEx] = values.toIndexedSeq

  /** Converts Java strings to a Scala sequence. */
  def strings(values: Array[String]): Seq[String] = values.toIndexedSeq

  /** Converts checked expression pairs to Scala tuples. */
  def checkedPairs(
      values: Array[ExpressionPair[TlaBuilderExpr]],
      stateOf: Function[TlaBuilderExpr, Object]): Seq[(TBuilderInstruction, TBuilderInstruction)] =
    values.toIndexedSeq.map(pair => checkedState(stateOf.apply(pair.first())) -> checkedState(stateOf.apply(pair.second())))

  /** Converts scope-unchecked expression pairs to Scala tuples. */
  def uncheckedPairs(values: Array[ExpressionPair[TlaEx]]): Seq[(TlaEx, TlaEx)] =
    values.toIndexedSeq.map(pair => pair.first() -> pair.second())

  /** Converts checked named expressions to Scala tuples. */
  def checkedNamed(
      values: Array[NamedExpression[TlaBuilderExpr]],
      stateOf: Function[TlaBuilderExpr, Object]): Seq[(String, TBuilderInstruction)] =
    values.toIndexedSeq.map(field => field.name() -> checkedState(stateOf.apply(field.expression())))

  /** Converts scope-unchecked named expressions to Scala tuples. */
  def uncheckedNamed(values: Array[NamedExpression[TlaEx]]): Seq[(String, TlaEx)] =
    values.toIndexedSeq.map(field => field.name() -> field.expression())

  /** Converts checked EXCEPT updates to Scala tuples. */
  def checkedUpdates(
      values: Array[ExceptUpdate[TlaBuilderExpr]],
      stateOf: Function[TlaBuilderExpr, Object]): Seq[(TBuilderInstruction, TBuilderInstruction)] =
    values.toIndexedSeq.map(update => checkedState(stateOf.apply(update.index())) -> checkedState(stateOf.apply(update.value())))

  /** Converts scope-unchecked EXCEPT updates to Scala tuples. */
  def uncheckedUpdates(values: Array[ExceptUpdate[TlaEx]]): Seq[(TlaEx, TlaEx)] =
    values.toIndexedSeq.map(update => update.index() -> update.value())

  /** Converts Java typed parameters to Scala typed parameters. */
  def typedParameters(values: Array[TypedParameter]): Seq[ParamUtil.TypedParam] =
    values.toIndexedSeq.map(param => ParamUtil.param(param.name(), param.`type`()))

  /** Converts operator parameters to a Scala sequence. */
  def operParameters(values: Array[OperParam]): Seq[OperParam] = values.toIndexedSeq

  /** Converts pending-declaration handles to the underlying builder instructions. */
  def checkedDecls(
      values: Array[TlaBuilderDecl],
      stateOf: Function[TlaBuilderDecl, Object]): Seq[TBuilderOperDeclInstruction] =
    values.toIndexedSeq.map(value => checkedDeclState(stateOf.apply(value)))

  /** Converts scope-unchecked declarations to a Scala sequence. */
  def uncheckedDecls(values: Array[TlaOperDecl]): Seq[TlaOperDecl] = values.toIndexedSeq

  /** Returns an absent checked row variable. */
  def noRowVariable: Option[String] = None

  /** Returns an absent scope-unchecked row variable. */
  def noUncheckedRowVariable: Option[VarT1] = None

  /** Materializes checked expression state as TLA+ IR. */
  def buildExpr(state: Object): TlaEx = at.forsyte.apalache.tla.typecomp.build(checkedState(state))

  /** Materializes checked declaration state as TLA+ IR. */
  def buildDecl(state: Object): TlaOperDecl =
    at.forsyte.apalache.tla.typecomp.build(checkedDeclState(state))

  /** Creates a constant type. */
  def constantType(name: String): ConstT1 = ConstT1(name)

  /** Creates a type variable from an index. */
  def typeVariable(index: Int): VarT1 = VarT1(index)

  /** Creates a type variable from a name. */
  def typeVariable(name: String): VarT1 = VarT1(name)

  /** Creates a function type. */
  def functionType(argument: TlaType1, result: TlaType1): FunT1 = FunT1(argument, result)

  /** Creates a set type. */
  def setType(element: TlaType1): SetT1 = SetT1(element)

  /** Creates a sequence type. */
  def sequenceType(element: TlaType1): SeqT1 = SeqT1(element)

  /** Creates a tuple type. */
  def tupleType(elements: Array[TlaType1]): TupT1 = TupT1(elements.toIndexedSeq: _*)

  /** Creates a sparse tuple type. */
  def sparseTupleType(fields: Array[IndexedType]): SparseTupT1 =
    SparseTupT1(SortedMap.from(fields.iterator.map(field => field.index() -> field.`type`())))

  /** Creates an operator type. */
  def operatorType(result: TlaType1, arguments: Array[TlaType1]): OperT1 =
    OperT1(arguments.toIndexedSeq, result)

  /** Creates the underlying row type. */
  private def rowType(other: Option[VarT1], fields: Array[NamedType]): RowT1 =
    RowT1(SortedMap.from(fields.iterator.map(field => field.name() -> field.`type`())), other)

  /** Creates a closed row type. */
  def closedRowType(fields: Array[NamedType]): RowT1 = rowType(None, fields)

  /** Creates an open row type. */
  def openRowType(other: String, fields: Array[NamedType]): RowT1 = rowType(Some(VarT1(other)), fields)

  /** Creates a closed row-record type. */
  def closedRowRecordType(fields: Array[NamedType]): RecRowT1 = RecRowT1(closedRowType(fields))

  /** Creates an open row-record type. */
  def openRowRecordType(other: String, fields: Array[NamedType]): RecRowT1 = RecRowT1(openRowType(other, fields))

  /** Creates a closed variant type. */
  def closedVariantType(fields: Array[NamedType]): VariantT1 = VariantT1(closedRowType(fields))

  /** Creates an open variant type. */
  def openVariantType(other: String, fields: Array[NamedType]): VariantT1 = VariantT1(openRowType(other, fields))

  /** Creates a typed constant declaration. */
  def constantDeclaration(name: String, tlaType: TlaType1): TlaConstDecl = TlaConstDecl(name)(Typed(tlaType))

  /** Creates a typed variable declaration. */
  def variableDeclaration(name: String, tlaType: TlaType1): TlaVarDecl = TlaVarDecl(name)(Typed(tlaType))
}
