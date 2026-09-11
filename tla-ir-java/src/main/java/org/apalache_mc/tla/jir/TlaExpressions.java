package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.*;
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker;
import at.forsyte.apalache.tla.lir.transformations.standard.DeepCopy;
import java.util.List;
import java.util.Objects;
import java.util.function.Consumer;
import java.util.function.UnaryOperator;
import scala.jdk.javaapi.CollectionConverters;

/**
 * Inspects, traverses, copies and edits typed TLA+ expressions.
 *
 * <p>Editing methods retain existing type information but do not infer types or validate lexical
 * scope. Use {@link TlaCheckedBuilder} when creating expressions from unvalidated inputs.</p>
 */
public final class TlaExpressions {
  private TlaExpressions() {}

  /** Immutable snapshot in operand order. Elements are not copied. */
  public static List<TlaEx> arguments(OperEx expression) {
    return List.copyOf(CollectionConverters.asJava(expression.args()));
  }

  /** Immutable snapshot in declaration order. Declarations remain mutable IR objects. */
  public static List<TlaOperDecl> localDeclarations(LetInEx expression) {
    return List.copyOf(CollectionConverters.asJava(expression.decls()));
  }

  /** Renames this occurrence, preserving its tag; this is not capture-avoiding substitution. */
  public static NameEx withName(NameEx expression, String name) {
    return NameEx.apply(Objects.requireNonNull(name), expression.typeTag());
  }

  /** Replaces operands without rechecking types; retains the original operator and tag. */
  public static OperEx withArguments(OperEx expression, List<? extends TlaEx> arguments) {
    var snapshot = List.<TlaEx>copyOf(arguments);
    return OperEx.apply(expression.oper(), CollectionConverters.asScala(snapshot).toSeq(), expression.typeTag());
  }

  /** Replaces local definitions, retaining the body and tag without copying them. */
  public static LetInEx withLocalDeclarations(LetInEx expression, List<TlaOperDecl> declarations) {
    var snapshot = List.copyOf(declarations);
    return LetInEx.apply(
        expression.body(), CollectionConverters.asScala(snapshot).toSeq(), expression.typeTag());
  }

  /** Wraps a body and existing definitions in LET, retaining the body's tag and all references. */
  public static LetInEx letIn(TlaEx body, List<TlaOperDecl> declarations) {
    var snapshot = List.copyOf(declarations);
    return LetInEx.apply(body, CollectionConverters.asScala(snapshot).toSeq(), body.typeTag());
  }

  /**
   * Visits occurrences in preorder, including LET body before local declaration bodies.
   * Shared occurrences are visited repeatedly. The callback must not mutate the traversed IR.
   */
  public static void forEach(TlaEx expression, Consumer<TlaEx> visit) {
    Objects.requireNonNull(visit).accept(expression);
    if (expression instanceof OperEx operation) {
      arguments(operation).forEach(argument -> forEach(argument, visit));
    } else if (expression instanceof LetInEx letIn) {
      forEach(letIn.body(), visit);
      localDeclarations(letIn).forEach(declaration -> forEach(declaration.body(), visit));
    }
  }

  /**
   * Rebuilds compound nodes and local declarations bottom-up, sharing unchanged leaves.
   * Preserves tags, arities and recursion flags. The callback sees each rebuilt node once;
   * its non-null result is not traversed again. This is not a fresh-ID deep copy, and a
   * callback that returns shared mutable nodes is responsible for their ownership.
   */
  public static TlaEx rewrite(TlaEx expression, UnaryOperator<TlaEx> replace) {
    Objects.requireNonNull(replace);
    TlaEx rebuilt;
    if (expression instanceof OperEx operation) {
      var rewrittenArguments = arguments(operation).stream().map(argument -> rewrite(argument, replace)).toList();
      rebuilt = withArguments(operation, rewrittenArguments);
    } else if (expression instanceof LetInEx letIn) {
      var rewrittenBody = rewrite(letIn.body(), replace);
      var rewrittenDeclarations = localDeclarations(letIn).stream()
          .map(declaration -> TlaDeclarations.rewrite(declaration, replace))
          .toList();
      rebuilt = LetInEx.apply(rewrittenBody,
          CollectionConverters.asScala(rewrittenDeclarations).toSeq(), expression.typeTag());
    } else {
      rebuilt = expression;
    }
    return Objects.requireNonNull(replace.apply(rebuilt), "replacement");
  }

  /**
   * Copies every copyable node with fresh IDs, including name/value leaves and local
   * declarations. Preserves tags and recursion flags. The special NullEx value may be shared.
   */
  public static TlaEx deepCopy(TlaEx expression) {
    return new DeepCopy(new IdleTracker()).deepCopyEx(expression);
  }
}
