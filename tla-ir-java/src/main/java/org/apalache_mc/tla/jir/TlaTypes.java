package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import org.apalache_mc.tla.jir.impl.JavaToScalaAdapter$;
import scala.Tuple2;
import scala.jdk.javaapi.CollectionConverters;

/**
 * Creates and inspects the types attached to TLA+ expressions and declarations.
 *
 * <p>Use the primitive constants for built-in types and the factory methods for sets,
 * functions, tuples, operators, records, rows and variants. Inspection methods return
 * immutable Java collections in a documented order.</p>
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

  /** Returns the expression's type; throws TlaBuilderTypeException for a non-Typed tag. */
  public static TlaType1 typeOf(TlaEx expression) {
    return typeOf(expression.typeTag());
  }

  /** Returns the declaration's type; throws TlaBuilderTypeException for a non-Typed tag. */
  public static TlaType1 typeOf(TlaDecl declaration) {
    return typeOf(declaration.typeTag());
  }

  private static TlaType1 typeOf(TypeTag tag) {
    if (tag instanceof Typed<?> typed && typed.myType() instanceof TlaType1 type) return type;
    throw new TlaBuilderTypeException("Expected a Typed tag, found: " + tag);
  }

  /**
   * Immediate children in structural order: positional arguments, then result; sorted fields,
   * then row tail. Record/variant wrappers have their row as their sole child. All core types
   * are supported, including legacy records and sparse tuples. The list is an immutable snapshot.
   */
  public static List<TlaType1> children(TlaType1 type) {
    if (type instanceof SetT1 set) return List.of(set.elem());
    if (type instanceof SeqT1 sequence) return List.of(sequence.elem());
    if (type instanceof FunT1 function) return List.of(function.arg(), function.res());
    if (type instanceof TupT1 tuple) return tupleElements(tuple);
    if (type instanceof OperT1 operator) {
      var children = new ArrayList<>(operatorArguments(operator));
      children.add(operator.res());
      return List.copyOf(children);
    }
    if (type instanceof RecRowT1 record) return List.of(record.row());
    if (type instanceof VariantT1 variant) return List.of(variant.row());
    if (type instanceof RowT1 row) {
      var children = new ArrayList<>(rowFields(row).values());
      rowTail(row).ifPresent(children::add);
      return List.copyOf(children);
    }
    if (type instanceof RecT1 record) {
      return List.copyOf(CollectionConverters.asJava(record.fieldTypes()).values());
    }
    if (type instanceof SparseTupT1 tuple) {
      return List.copyOf(CollectionConverters.asJava(tuple.fieldTypes()).values());
    }
    if (type == INT || type == BOOL || type == REAL || type == STRING
        || type instanceof ConstT1 || type instanceof VarT1) {
      return List.of();
    }
    throw new IllegalArgumentException("Unsupported TLA+ type: " + type);
  }

  /** Immutable snapshot in tuple position order. */
  public static List<TlaType1> tupleElements(TupT1 type) {
    return List.copyOf(CollectionConverters.asJava(type.elems()));
  }

  /** Immutable snapshot in parameter order, excluding the result type. */
  public static List<TlaType1> operatorArguments(OperT1 type) {
    return List.copyOf(CollectionConverters.asJava(type.args()));
  }

  /** Immutable snapshot sorted by field name. */
  public static SortedMap<String, TlaType1> rowFields(RowT1 type) {
    var fields = new TreeMap<String, TlaType1>();
    fields.putAll(CollectionConverters.asJava(type.fieldTypes()));
    return Collections.unmodifiableSortedMap(fields);
  }

  /** The residual variable of an open row, or empty for a closed row. */
  public static Optional<VarT1> rowTail(RowT1 type) {
    return type.other().isEmpty() ? Optional.empty() : Optional.of(type.other().get());
  }

  /** Immutable set of variable IDs; iteration order is unspecified. */
  public static Set<Integer> usedVariables(TlaType1 type) {
    var names = CollectionConverters.asJava(type.usedNames());
    return names.stream()
        .map(name -> ((Number) name).intValue())
        .collect(java.util.stream.Collectors.toUnmodifiableSet());
  }

  /** Creates an open row without converting its variable ID to a string. */
  public static RowT1 row(VarT1 other, NamedType... fields) {
    var entries = new ArrayList<Tuple2<String, TlaType1>>(fields.length);
    for (var field : fields) entries.add(new Tuple2<>(field.name(), field.type()));
    return RowT1.apply(other, CollectionConverters.asScala(entries).toSeq());
  }

  /** Creates an open row-record without converting its variable ID to a string. */
  public static RecRowT1 rowRecord(VarT1 other, NamedType... fields) {
    return new RecRowT1(row(other, fields));
  }

  /** Creates an open variant without converting its variable ID to a string. */
  public static VariantT1 variant(VarT1 other, NamedType... fields) {
    return new VariantT1(row(other, fields));
  }

  /** Prevents instantiation. */
  private TlaTypes() {}

  /**
   * Returns an uninterpreted constant type with the supplied name.
   *
   * @param name the type name, such as {@code Process}
   * @return the named constant type
   */
  public static ConstT1 constant(String name) {
    return JavaToScalaAdapter$.MODULE$.constantType(name);
  }

  /**
   * Returns the type variable identified by a numeric index.
   *
   * @param index a nonnegative type-variable index; indices {@code 0} through {@code 25} correspond to {@code a}
   *     through {@code z}
   * @return the type variable
   */
  public static VarT1 typeVariable(int index) {
    return JavaToScalaAdapter$.MODULE$.typeVariable(index);
  }

  /**
   * Returns the type variable identified by a name.
   *
   * @param name a lower-case letter from {@code a} through {@code z}, or {@code a} followed by a nonnegative integer
   * @return the type variable
   */
  public static VarT1 typeVariable(String name) {
    return JavaToScalaAdapter$.MODULE$.typeVariable(name);
  }

  /**
   * Returns the type of functions from {@code argument} to {@code result}.
   *
   * @param argument the domain element type
   * @param result the range element type
   * @return the function type
   */
  public static FunT1 function(TlaType1 argument, TlaType1 result) {
    return JavaToScalaAdapter$.MODULE$.functionType(argument, result);
  }

  /**
   * Returns the type of sets whose members have {@code element} type.
   *
   * @param element the element type
   * @return the set type
   */
  public static SetT1 set(TlaType1 element) {
    return JavaToScalaAdapter$.MODULE$.setType(element);
  }

  /**
   * Returns the type of sequences whose elements have {@code element} type.
   *
   * @param element the element type
   * @return the sequence type
   */
  public static SeqT1 sequence(TlaType1 element) {
    return JavaToScalaAdapter$.MODULE$.sequenceType(element);
  }

  /**
   * Returns a tuple type with one type for each position.
   *
   * @param elements the position types, in tuple order
   * @return the tuple type
   */
  public static TupT1 tuple(TlaType1... elements) {
    return JavaToScalaAdapter$.MODULE$.tupleType(elements);
  }

  /**
   * Returns a sparse tuple type containing the specified indexed fields.
   *
   * @param fields the present tuple positions and their types
   * @return the sparse-tuple type
   */
  public static SparseTupT1 sparseTuple(IndexedType... fields) {
    return JavaToScalaAdapter$.MODULE$.sparseTupleType(fields);
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
    return JavaToScalaAdapter$.MODULE$.operatorType(result, arguments);
  }

  /**
   * Returns a closed row containing exactly the specified fields.
   *
   * @param fields the row field names and types
   * @return the row type
   */
  public static RowT1 row(NamedType... fields) {
    return JavaToScalaAdapter$.MODULE$.closedRowType(fields);
  }

  /**
   * Returns an open row that may contain fields beyond those specified.
   *
   * @param other the type variable representing the unspecified remainder of the row
   * @param fields the known row field names and types
   * @return the row type
   */
  public static RowT1 row(String other, NamedType... fields) {
    return JavaToScalaAdapter$.MODULE$.openRowType(other, fields);
  }

  /**
   * Returns a row-record type containing exactly the specified fields.
   *
   * @param fields the record field names and types
   * @return the row-record type
   */
  public static RecRowT1 rowRecord(NamedType... fields) {
    return JavaToScalaAdapter$.MODULE$.closedRowRecordType(fields);
  }

  /**
   * Returns a row-record type that may contain fields beyond those specified.
   *
   * @param other the type variable representing the unspecified remainder of the record
   * @param fields the known record field names and types
   * @return the row-record type
   */
  public static RecRowT1 rowRecord(String other, NamedType... fields) {
    return JavaToScalaAdapter$.MODULE$.openRowRecordType(other, fields);
  }

  /**
   * Returns a variant type containing exactly the specified alternatives.
   *
   * @param fields the variant tags and their value types
   * @return the variant type
   */
  public static VariantT1 variant(NamedType... fields) {
    return JavaToScalaAdapter$.MODULE$.closedVariantType(fields);
  }

  /**
   * Returns a variant type that may contain alternatives beyond those specified.
   *
   * @param other the type variable representing the unspecified alternatives
   * @param fields the known variant tags and their value types
   * @return the variant type
   */
  public static VariantT1 variant(String other, NamedType... fields) {
    return JavaToScalaAdapter$.MODULE$.openVariantType(other, fields);
  }
}
