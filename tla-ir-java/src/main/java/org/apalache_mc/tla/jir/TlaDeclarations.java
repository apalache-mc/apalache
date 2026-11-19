package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.*;
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker;
import at.forsyte.apalache.tla.lir.transformations.standard.DeepCopy;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.UnaryOperator;
import org.apalache_mc.tla.jir.impl.JavaToScalaAdapter$;
import scala.jdk.javaapi.CollectionConverters;

/**
 * Creates and edits declarations in typed TLA+ modules.
 *
 * <p>The structural editing methods preserve the declaration's existing type information,
 * parameter arities and recursion marker. They do not type-check a replacement body; use a
 * checked builder when constructing declarations from unvalidated inputs.</p>
 */
public final class TlaDeclarations {
  /**
   * Returns the declaration's parameter names and types in declaration order.
   *
   * @throws TlaBuilderTypeException if its stored operator type does not agree with its parameters
   */
  public static List<TypedParameter> parameters(TlaOperDecl declaration) {
    var type = TlaTypes.typeOf(declaration);
    if (!(type instanceof OperT1 operatorType)
        || operatorType.args().size() != declaration.formalParams().size()) {
      throw new TlaBuilderTypeException(
          "Expected an operator signature matching parameters: " + declaration.name());
    }

    var formalParameters = CollectionConverters.asJava(declaration.formalParams());
    var parameterTypes = CollectionConverters.asJava(operatorType.args());
    var result = new ArrayList<TypedParameter>(formalParameters.size());
    for (var index = 0; index < formalParameters.size(); index++) {
      var parameter = formalParameters.get(index);
      var parameterType = parameterTypes.get(index);
      var arity = parameterType instanceof OperT1 nestedOperator ? nestedOperator.args().size() : 0;
      if (parameter.arity() != arity) {
        throw new TlaBuilderTypeException("Parameter arity mismatch: " + parameter.name());
      }
      result.add(new TypedParameter(parameter.name(), parameterType));
    }
    return List.copyOf(result);
  }

  /** Replaces the body without type checking, retaining the tag, parameters and recursion flag. */
  public static TlaOperDecl withBody(TlaOperDecl declaration, TlaEx body) {
    return declaration.copy(
        declaration.name(), declaration.formalParams(), Objects.requireNonNull(body), declaration.typeTag());
  }

  /**
   * Renames the declaration and its parameters without rewriting its body. Parameter count
   * must be unchanged; arities, type tag, body and recursion flag are retained.
   */
  public static TlaOperDecl withHeader(
      TlaOperDecl declaration, String name, List<String> parameterNames) {
    Objects.requireNonNull(name);
    var names = List.copyOf(parameterNames);
    var oldParameters = CollectionConverters.asJava(declaration.formalParams());
    if (names.size() != oldParameters.size()) {
      throw new IllegalArgumentException("Parameter count must not change");
    }
    var newParameters = new ArrayList<OperParam>(names.size());
    for (var index = 0; index < names.size(); index++) {
      newParameters.add(OperParam.apply(names.get(index), oldParameters.get(index).arity()));
    }
    return declaration.copy(name, CollectionConverters.asScala(newParameters).toList(),
        declaration.body(), declaration.typeTag());
  }

  /** Rebuilds the body bottom-up as in TlaExpressions.rewrite, preserving declaration metadata. */
  public static TlaOperDecl rewrite(TlaOperDecl declaration, UnaryOperator<TlaEx> replace) {
    return withBody(declaration, TlaExpressions.rewrite(declaration.body(), Objects.requireNonNull(replace)));
  }

  /** Copies a declaration and all copyable expression nodes with fresh IDs. */
  public static <D extends TlaDecl> D deepCopy(D declaration) {
    return new DeepCopy(new IdleTracker()).deepCopyDecl(declaration);
  }

  /** Prevents instantiation. */
  private TlaDeclarations() {}

  /**
   * Returns a declaration for a TLA+ constant with the supplied type.
   *
   * @param name the constant name as it appears in TLA+
   * @param type the constant's type
   * @return the typed constant declaration
   */
  public static TlaConstDecl constant(String name, TlaType1 type) {
    return JavaToScalaAdapter$.MODULE$.constantDeclaration(name, type);
  }

  /**
   * Returns a declaration for a TLA+ variable with the supplied type.
   *
   * @param name the variable name as it appears in TLA+
   * @param type the variable's type
   * @return the typed variable declaration
   */
  public static TlaVarDecl variable(String name, TlaType1 type) {
    return JavaToScalaAdapter$.MODULE$.variableDeclaration(name, type);
  }
}
