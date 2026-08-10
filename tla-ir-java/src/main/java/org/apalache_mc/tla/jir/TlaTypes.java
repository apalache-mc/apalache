package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.BoolT1$;
import at.forsyte.apalache.tla.lir.ConstT1;
import at.forsyte.apalache.tla.lir.FunT1;
import at.forsyte.apalache.tla.lir.IntT1$;
import at.forsyte.apalache.tla.lir.OperT1;
import at.forsyte.apalache.tla.lir.RealT1$;
import at.forsyte.apalache.tla.lir.RecRowT1;
import at.forsyte.apalache.tla.lir.RowT1;
import at.forsyte.apalache.tla.lir.SeqT1;
import at.forsyte.apalache.tla.lir.SetT1;
import at.forsyte.apalache.tla.lir.SparseTupT1;
import at.forsyte.apalache.tla.lir.StrT1$;
import at.forsyte.apalache.tla.lir.TlaType1;
import at.forsyte.apalache.tla.lir.TupT1;
import at.forsyte.apalache.tla.lir.VarT1;
import at.forsyte.apalache.tla.lir.VariantT1;
import org.apalache_mc.tla.jir.impl.JavaFacadeSupport$;

/**
 * Creates the TLA+ types accepted by the builders and declaration factories.
 *
 * <p>Use the shared primitive constants directly and the static factory methods for parameterized or structured
 * types. Every returned value is an Apalache {@code TlaType1} that can be attached to names, declarations, and
 * explicitly typed expressions.</p>
 */
public final class TlaTypes {
  /** The TLA+ integer type. */
  public static final TlaType1 INT = IntT1$.MODULE$;

  /** The TLA+ real-number type. */
  public static final TlaType1 REAL = RealT1$.MODULE$;

  /** The TLA+ Boolean type. */
  public static final TlaType1 BOOL = BoolT1$.MODULE$;

  /** The TLA+ string type. */
  public static final TlaType1 STRING = StrT1$.MODULE$;

  /** Prevents instantiation. */
  private TlaTypes() {}

  /**
   * Returns an uninterpreted constant type with the supplied name.
   *
   * @param name the type name, such as {@code Process}
   * @return the named constant type
   */
  public static ConstT1 constant(String name) {
    return JavaFacadeSupport$.MODULE$.constantType(name);
  }

  /**
   * Returns the type variable identified by a numeric index.
   *
   * @param index a nonnegative type-variable index; indices {@code 0} through {@code 25} correspond to {@code a}
   *     through {@code z}
   * @return the type variable
   */
  public static VarT1 typeVariable(int index) {
    return JavaFacadeSupport$.MODULE$.typeVariable(index);
  }

  /**
   * Returns the type variable identified by a name.
   *
   * @param name a lower-case letter from {@code a} through {@code z}, or {@code a} followed by a nonnegative integer
   * @return the type variable
   */
  public static VarT1 typeVariable(String name) {
    return JavaFacadeSupport$.MODULE$.typeVariable(name);
  }

  /**
   * Returns the type of functions from {@code argument} to {@code result}.
   *
   * @param argument the domain element type
   * @param result the range element type
   * @return the function type
   */
  public static FunT1 function(TlaType1 argument, TlaType1 result) {
    return JavaFacadeSupport$.MODULE$.functionType(argument, result);
  }

  /**
   * Returns the type of sets whose members have {@code element} type.
   *
   * @param element the element type
   * @return the set type
   */
  public static SetT1 set(TlaType1 element) {
    return JavaFacadeSupport$.MODULE$.setType(element);
  }

  /**
   * Returns the type of sequences whose elements have {@code element} type.
   *
   * @param element the element type
   * @return the sequence type
   */
  public static SeqT1 sequence(TlaType1 element) {
    return JavaFacadeSupport$.MODULE$.sequenceType(element);
  }

  /**
   * Returns a tuple type with one type for each position.
   *
   * @param elements the position types, in tuple order
   * @return the tuple type
   */
  public static TupT1 tuple(TlaType1... elements) {
    return JavaFacadeSupport$.MODULE$.tupleType(elements);
  }

  /**
   * Returns a sparse tuple type containing the specified indexed fields.
   *
   * @param fields the present tuple positions and their types
   * @return the sparse-tuple type
   */
  public static SparseTupT1 sparseTuple(IndexedType... fields) {
    return JavaFacadeSupport$.MODULE$.sparseTupleType(fields);
  }

  /**
   * Returns an operator type.
   *
   * <p>The result type comes first because Java only permits a varargs parameter in the final position.</p>
   *
   * @param result the operator's result type
   * @param arguments the operator's parameter types, in declaration order
   * @return the operator type
   */
  public static OperT1 operator(TlaType1 result, TlaType1... arguments) {
    return JavaFacadeSupport$.MODULE$.operatorType(result, arguments);
  }

  /**
   * Returns a closed row containing exactly the specified fields.
   *
   * @param fields the row field names and types
   * @return the row type
   */
  public static RowT1 row(NamedType... fields) {
    return JavaFacadeSupport$.MODULE$.closedRowType(fields);
  }

  /**
   * Returns an open row that may contain fields beyond those specified.
   *
   * @param other the type variable representing the unspecified remainder of the row
   * @param fields the known row field names and types
   * @return the row type
   */
  public static RowT1 row(String other, NamedType... fields) {
    return JavaFacadeSupport$.MODULE$.openRowType(other, fields);
  }

  /**
   * Returns a row-record type containing exactly the specified fields.
   *
   * @param fields the record field names and types
   * @return the row-record type
   */
  public static RecRowT1 rowRecord(NamedType... fields) {
    return JavaFacadeSupport$.MODULE$.closedRowRecordType(fields);
  }

  /**
   * Returns a row-record type that may contain fields beyond those specified.
   *
   * @param other the type variable representing the unspecified remainder of the record
   * @param fields the known record field names and types
   * @return the row-record type
   */
  public static RecRowT1 rowRecord(String other, NamedType... fields) {
    return JavaFacadeSupport$.MODULE$.openRowRecordType(other, fields);
  }

  /**
   * Returns a variant type containing exactly the specified alternatives.
   *
   * @param fields the variant tags and their value types
   * @return the variant type
   */
  public static VariantT1 variant(NamedType... fields) {
    return JavaFacadeSupport$.MODULE$.closedVariantType(fields);
  }

  /**
   * Returns a variant type that may contain alternatives beyond those specified.
   *
   * @param other the type variable representing the unspecified alternatives
   * @param fields the known variant tags and their value types
   * @return the variant type
   */
  public static VariantT1 variant(String other, NamedType... fields) {
    return JavaFacadeSupport$.MODULE$.openVariantType(other, fields);
  }
}
