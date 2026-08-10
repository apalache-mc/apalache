package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.ConstT1;
import at.forsyte.apalache.tla.lir.OperParam;
import at.forsyte.apalache.tla.lir.TlaEx;
import at.forsyte.apalache.tla.lir.TlaOperDecl;
import at.forsyte.apalache.tla.lir.TlaType1;
import at.forsyte.apalache.tla.lir.TlaVarDecl;
import at.forsyte.apalache.tla.lir.VariantT1;
import at.forsyte.apalache.tla.typecomp.ScopedBuilder;
import java.math.BigInteger;
import java.util.concurrent.Callable;
import org.apalache_mc.tla.jir.impl.JavaFacadeSupport$;
import scala.collection.immutable.Seq;
import scalaz.IndexedStateT;

/**
 * Builds typed TLA+ IR while checking both operand types and lexical scope.
 *
 * <p>Builder operations return opaque {@link TlaBuilderExpr} and {@link TlaBuilderDecl} values that can be composed
 * safely. Call {@code build} when the expression or declaration is complete; validation then produces the
 * corresponding IR value. Invalid types raise {@link TlaBuilderTypeException}, and invalid name usage raises
 * {@link TlaBuilderScopeException}.</p>
 *
 * <p>This is the recommended builder when constructing new expressions. Use {@link TlaTypedScopeUncheckedBuilder}
 * only when the caller already guarantees correct lexical scoping.</p>
 */
@SuppressWarnings({"rawtypes", "unchecked", "unused"})
public final class TlaCheckedBuilder {
  private final ScopedBuilder builder;

  /**
   * Creates a builder that enforces the type, scope, and structural requirements of every operation.
   */
  public TlaCheckedBuilder() {
    this(true);
  }

  /**
   * Creates a builder and selects whether Apalache-specific structural requirements are enforced.
   *
   * <p>Type and scope checks are always enabled. Strict mode additionally checks requirements that are not expressible
   * in TLA+ types, such as requiring {@code assign}'s left side to be a primed variable and requiring {@code repeat}'s
   * operator argument to have the expected declaration shape.</p>
   *
   * @param strict {@code true} to enable the additional structural checks on Apalache-specific operations;
   *     {@code false} to omit those additional checks
   */
  public TlaCheckedBuilder(boolean strict) {
    builder = new ScopedBuilder(strict);
  }

  /**
   * Validates a pending expression and returns its typed TLA+ IR form.
   *
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx build(TlaBuilderExpr expression) {
    return call(() -> JavaFacadeSupport$.MODULE$.buildExpr(expression.state()));
  }

  /**
   * Validates a pending operator declaration and returns its typed TLA+ IR form.
   *
   * @param declaration the declaration
   * @return the typed TLA+ IR operator declaration
   */
  public TlaOperDecl build(TlaBuilderDecl declaration) {
    return call(() -> JavaFacadeSupport$.MODULE$.buildDecl(declaration.state()));
  }

  /**
   * Imports an existing IR expression as already validated so it can be composed with pending expressions.
   *
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr unchecked(TlaEx expression) {
    return expression(() -> builder.unchecked(expression));
  }

  /**
   * Imports an existing IR declaration as already validated so it can be used with pending expressions.
   *
   * @param declaration the declaration
   * @return the pending operator declaration
   */
  public TlaBuilderDecl uncheckedDecl(TlaOperDecl declaration) {
    return declaration(() -> builder.uncheckedDecl(declaration));
  }

  /**
   * Creates an integer literal.
   *
   * <p>Example TLA+: {@code 42}.</p>
   *
   * @param value the value
   * @return the pending expression
   */
  public TlaBuilderExpr integer(BigInteger value) {
    return expression(
        () -> JavaFacadeSupport$.MODULE$.checkedInteger(
            builder, JavaFacadeSupport$.MODULE$.bigInt(value)));
  }

  /**
   * Creates an integer literal.
   *
   * <p>Example TLA+: {@code 42, -128}.</p>
   *
   * @param value the value
   * @return the pending expression
   */
  public TlaBuilderExpr integer(long value) {
    return integer(BigInteger.valueOf(value));
  }

  /**
   * Creates a TLA+ string literal.
   *
   * <p>Example TLA+: {@code "ready"}.</p>
   *
   * @param value the value
   * @return the pending expression
   */
  public TlaBuilderExpr str(String value) {
    return expression(() -> builder.str(value));
  }

  /**
   * Creates a Boolean literal.
   *
   * <p>Example TLA+: {@code FALSE, TRUE}.</p>
   *
   * @param value the value
   * @return the pending expression
   */
  public TlaBuilderExpr bool(boolean value) {
    return expression(() -> builder.bool(value));
  }

  /**
   * Creates a model value from a root name and an uninterpreted constant type.
   *
   * <p>Example TLA+: {@code red_OF_Color}.</p>
   *
   * @param root the model-value root, without an {@code _OF_} suffix
   * @param type the model value's uninterpreted constant type
   * @return the pending expression
   */
  public TlaBuilderExpr constant(String root, ConstT1 type) {
    return expression(() -> JavaFacadeSupport$.MODULE$.checkedConstant(builder, root, type));
  }

  /**
   * Creates a model value from its encoded name, such as {@code 1_OF_Process}.
   *
   * <p>Example TLA+: {@code red_OF_Color}.</p>
   *
   * @param value the complete encoded model-value name
   * @return the pending expression
   */
  public TlaBuilderExpr constParsed(String value) {
    return expression(() -> builder.constParsed(value));
  }

  /**
   * Creates the built-in TLA+ set {@code BOOLEAN}.
   *
   * <p>Example TLA+: {@code BOOLEAN}.</p>
   *
   * @return the pending expression
   */
  public TlaBuilderExpr booleanSet() {
    return expression(builder::booleanSet);
  }

  /**
   * Creates the built-in TLA+ set {@code STRING}.
   *
   * <p>Example TLA+: {@code STRING}.</p>
   *
   * @return the pending expression
   */
  public TlaBuilderExpr stringSet() {
    return expression(builder::stringSet);
  }

  /**
   * Creates the built-in TLA+ set {@code Int}.
   *
   * <p>Example TLA+: {@code Int}.</p>
   *
   * @return the pending expression
   */
  public TlaBuilderExpr intSet() {
    return expression(builder::intSet);
  }

  /**
   * Creates the built-in TLA+ set {@code Nat}.
   *
   * <p>Example TLA+: {@code Nat}.</p>
   *
   * @return the pending expression
   */
  public TlaBuilderExpr natSet() {
    return expression(builder::natSet);
  }

  /**
   * Creates a reference to a TLA+ name with an explicit type.
   *
   * <p>Example TLA+: {@code counter}.</p>
   *
   * @param name the referenced TLA+ name
   * @param type the type assigned to that name
   * @return the pending expression
   */
  public TlaBuilderExpr name(String name, TlaType1 type) {
    return expression(() -> builder.name(name, type));
  }

  /**
   * Creates a reference whose type is inferred from earlier uses of the name in this expression.
   *
   * <p>Example TLA+: {@code counter}.</p>
   *
   * @param name the previously used name whose type is inferred
   * @return the pending expression
   */
  public TlaBuilderExpr nameWithInferredType(String name) {
    return expression(() -> builder.nameWithInferredType(name));
  }

  /**
   * Describes a typed parameter for an operator declaration or lambda.
   *
   * @param name the parameter name used in the operator body
   * @param type the parameter's value or operator type
   * @return the typed operator parameter
   */
  public TypedParameter param(String name, TlaType1 type) {
    return call(
        () -> {
          builder.param(name, type);
          return new TypedParameter(name, type);
        });
  }

  /**
   * Creates a TLA+ operator declaration with explicitly typed parameters.
   *
   * <p>Example TLA+: {@code Inc(x) == x + 1}.</p>
   *
   * @param name the declared operator name
   * @param body the operator body
   * @param parameters the operator parameters
   * @return the pending operator declaration
   */
  public TlaBuilderDecl decl(String name, TlaBuilderExpr body, TypedParameter... parameters) {
    return declaration(
        () -> builder.decl(name, state(body), JavaFacadeSupport$.MODULE$.typedParameters(parameters)));
  }

  /**
   * Creates an operator declaration and infers each parameter type from its use in the body.
   *
   * <p>Example TLA+: {@code Inc(x) == x + 1}.</p>
   *
   * @param name the declared operator name
   * @param body the operator body
   * @param parameters the operator parameters whose types are inferred
   * @return the pending operator declaration
   */
  public TlaBuilderDecl declWithInferredParameterTypes(
      String name, TlaBuilderExpr body, OperParam... parameters) {
    return declaration(
        () ->
            builder.declWithInferredParameterTypes(
                name, state(body), JavaFacadeSupport$.MODULE$.operParameters(parameters)));
  }

  /**
   * Creates a first-class operator value with explicitly typed parameters.
   * <p>The caller must choose a name that is unique among enclosing and nested lambdas.</p>
   *
   * <p>Example TLA+: {@code LAMBDA x: x + 1}.</p>
   *
   * @param uniqueName a caller-supplied name unique to this operator value
   * @param body the operator body
   * @param parameters the operator parameters
   * @return the pending expression
   */
  public TlaBuilderExpr lambda(
      String uniqueName, TlaBuilderExpr body, TypedParameter... parameters) {
    return expression(
        () -> builder.lambda(
            uniqueName, state(body), JavaFacadeSupport$.MODULE$.typedParameters(parameters)));
  }

  /**
   * Creates a TLA+ {@code LET ... IN ...} expression containing the supplied local declarations.
   *
   * <p>Example TLA+: {@code LET Inc(x) == x + 1 IN Inc(2)}.</p>
   *
   * @param body the expression evaluated with the local declarations in scope
   * @param declarations one or more local operator declarations
   * @return the pending expression
   */
  public TlaBuilderExpr letIn(TlaBuilderExpr body, TlaBuilderDecl... declarations) {
    return expression(
        () ->
            builder.letIn(
                state(body),
                JavaFacadeSupport$.MODULE$.checkedDecls(declarations, TlaBuilderDecl::state)));
  }

  /**
   * Creates nested TLA+ {@code EXCEPT} updates, applying the supplied replacements from left to right.
   *
   * <p>Example TLA+: {@code [f EXCEPT ![1] = 10, ![2] = 20]}.</p>
   *
   * @param function the function expression
   * @param updates one or more index/replacement pairs, applied in order
   * @return the pending expression
   */
  @SafeVarargs
  public final TlaBuilderExpr exceptMany(
      TlaBuilderExpr function, ExceptUpdate<TlaBuilderExpr>... updates) {
    return expression(
        () ->
            builder.exceptMany(
                state(function),
                JavaFacadeSupport$.MODULE$.checkedUpdates(updates, TlaBuilderExpr::state)));
  }

  /**
   * Creates a name reference using the name and type of an existing variable declaration.
   *
   * <p>Example TLA+: {@code counter}.</p>
   *
   * @param declaration the declaration
   * @return the pending expression
   */
  public TlaBuilderExpr varDeclAsNameEx(TlaVarDecl declaration) {
    return expression(() -> builder.varDeclAsNameEx(declaration));
  }

  /**
   * Creates the action formula {@code lhs' = rhs}.
   *
   * <p>Example TLA+: {@code counter' = counter + 1}.</p>
   *
   * @param lhs the unprimed left-hand expression
   * @param rhs the value compared with the primed left-hand expression
   * @return the pending expression
   */
  public TlaBuilderExpr primeEq(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.primeEq(state(lhs), state(rhs)));
  }

  /**
   * Creates the equality comparison {@code lhs = rhs}.
   *
   * <p>Example TLA+: {@code x = y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr eql(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.eql(state(lhs), state(rhs)));
  }

  /**
   * Creates the inequality comparison {@code lhs /= rhs}.
   *
   * <p>Example TLA+: {@code x /= y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr neql(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.neql(state(lhs), state(rhs)));
  }

  /**
   * Applies an operator value to zero or more arguments.
   *
   * <p>Example TLA+: {@code Max(x, y)}.</p>
   *
   * @param operator an operator-valued expression
   * @param arguments the argument expressions
   * @return the pending expression
   */
  public TlaBuilderExpr operApply(TlaBuilderExpr operator, TlaBuilderExpr... arguments) {
    return expression(() -> builder.appOp(state(operator), expressions(arguments)));
  }

  /**
   * Creates the unbounded choice {@code CHOOSE name : predicate}.
   *
   * <p>Example TLA+: {@code CHOOSE x: P(x)}.</p>
   *
   * @param name the bound name expression
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr choose(TlaBuilderExpr name, TlaBuilderExpr predicate) {
    return expression(() -> builder.choose(state(name), state(predicate)));
  }

  /**
   * Creates the bounded choice {@code CHOOSE name \in set : predicate}.
   *
   * <p>Example TLA+: {@code CHOOSE x \in S: P(x)}.</p>
   *
   * @param name the bound name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr choose(
      TlaBuilderExpr name, TlaBuilderExpr set, TlaBuilderExpr predicate) {
    return expression(() -> builder.choose(state(name), state(set), state(predicate)));
  }

  /**
   * Attaches a TLA+ label and its string arguments to an expression.
   *
   * <p>Example TLA+: {@code Step(i):: counter' = counter + 1}.</p>
   *
   * @param expression the expression
   * @param arguments one or more string components of the label
   * @return the pending expression
   */
  public TlaBuilderExpr label(TlaBuilderExpr expression, String... arguments) {
    return expression(
        () -> builder.label(state(expression), JavaFacadeSupport$.MODULE$.strings(arguments)));
  }

  /**
   * Creates the conjunction of the supplied Boolean expressions.
   *
   * <p>Example TLA+: {@code P /\ Q}.</p>
   *
   * @param arguments the argument expressions
   * @return the pending expression
   */
  public TlaBuilderExpr and(TlaBuilderExpr... arguments) {
    return expression(() -> builder.and(expressions(arguments)));
  }

  /**
   * Creates the disjunction of the supplied Boolean expressions.
   *
   * <p>Example TLA+: {@code P \/ Q}.</p>
   *
   * @param arguments the argument expressions
   * @return the pending expression
   */
  public TlaBuilderExpr or(TlaBuilderExpr... arguments) {
    return expression(() -> builder.or(expressions(arguments)));
  }

  /**
   * Creates the negation of a Boolean expression.
   *
   * <p>Example TLA+: {@code ~P}.</p>
   *
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr not(TlaBuilderExpr predicate) {
    return expression(() -> builder.not(state(predicate)));
  }

  /**
   * Creates the Boolean implication {@code lhs => rhs}.
   *
   * <p>Example TLA+: {@code P => Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr implies(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.impl(state(lhs), state(rhs)));
  }

  /**
   * Creates the Boolean equivalence {@code lhs <=> rhs}.
   *
   * <p>Example TLA+: {@code P <=> Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr equiv(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.equiv(state(lhs), state(rhs)));
  }

  /**
   * Creates universal quantification with the name bounded by a set.
   *
   * <p>Example TLA+: {@code \A x \in S: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr forall(
      TlaBuilderExpr name, TlaBuilderExpr set, TlaBuilderExpr predicate) {
    return expression(() -> builder.forall(state(name), state(set), state(predicate)));
  }

  /**
   * Creates unbounded universal quantification over a name.
   *
   * <p>Example TLA+: {@code \A x: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr forall(TlaBuilderExpr name, TlaBuilderExpr predicate) {
    return expression(() -> builder.forall(state(name), state(predicate)));
  }

  /**
   * Creates existential quantification with the name bounded by a set.
   *
   * <p>Example TLA+: {@code \E x \in S: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr exists(
      TlaBuilderExpr name, TlaBuilderExpr set, TlaBuilderExpr predicate) {
    return expression(() -> builder.exists(state(name), state(set), state(predicate)));
  }

  /**
   * Creates unbounded existential quantification over a name.
   *
   * <p>Example TLA+: {@code \E x: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr exists(TlaBuilderExpr name, TlaBuilderExpr predicate) {
    return expression(() -> builder.exists(state(name), state(predicate)));
  }

  /**
   * Creates integer addition {@code lhs + rhs}.
   *
   * <p>Example TLA+: {@code x + y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr plus(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.plus(state(lhs), state(rhs)));
  }

  /**
   * Creates integer subtraction {@code lhs - rhs}.
   *
   * <p>Example TLA+: {@code x - y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr minus(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.minus(state(lhs), state(rhs)));
  }

  /**
   * Creates integer negation {@code -value}.
   *
   * <p>Example TLA+: {@code -x}.</p>
   *
   * @param value the value expression
   * @return the pending expression
   */
  public TlaBuilderExpr uminus(TlaBuilderExpr value) {
    return expression(() -> builder.uminus(state(value)));
  }

  /**
   * Creates integer multiplication {@code lhs * rhs}.
   *
   * <p>Example TLA+: {@code x * y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr mult(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.mult(state(lhs), state(rhs)));
  }

  /**
   * Creates integer division {@code lhs \div rhs}.
   *
   * <p>Example TLA+: {@code x \div y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr div(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.div(state(lhs), state(rhs)));
  }

  /**
   * Creates the integer remainder {@code lhs % rhs}.
   *
   * <p>Example TLA+: {@code x % y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr mod(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.mod(state(lhs), state(rhs)));
  }

  /**
   * Creates integer exponentiation {@code lhs ^ rhs}.
   *
   * <p>Example TLA+: {@code x ^ y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr exp(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.exp(state(lhs), state(rhs)));
  }

  /**
   * Creates the inclusive integer interval {@code lhs .. rhs}.
   *
   * <p>Example TLA+: {@code 1 .. 10}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr interval(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.dotdot(state(lhs), state(rhs)));
  }

  /**
   * Creates the integer comparison {@code lhs < rhs}.
   *
   * <p>Example TLA+: {@code x < y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr lt(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.lt(state(lhs), state(rhs)));
  }

  /**
   * Creates the integer comparison {@code lhs > rhs}.
   *
   * <p>Example TLA+: {@code x > y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr gt(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.gt(state(lhs), state(rhs)));
  }

  /**
   * Creates the integer comparison {@code lhs <= rhs}.
   *
   * <p>Example TLA+: {@code x <= y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr le(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.le(state(lhs), state(rhs)));
  }

  /**
   * Creates the integer comparison {@code lhs >= rhs}.
   *
   * <p>Example TLA+: {@code x >= y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr ge(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.ge(state(lhs), state(rhs)));
  }

  /**
   * Creates an explicitly enumerated set from the supplied elements.
   *
   * <p>Example TLA+: {@code {1, 2, 3}}.</p>
   *
   * @param arguments the argument expressions
   * @return the pending expression
   */
  public TlaBuilderExpr enumSet(TlaBuilderExpr... arguments) {
    return expression(() -> builder.enumSet(expressions(arguments)));
  }

  /**
   * Creates an empty set with an explicit element type.
   *
   * <p>Example TLA+: {@code {}}.</p>
   *
   * @param elementType the element type
   * @return the pending expression
   */
  public TlaBuilderExpr emptySet(TlaType1 elementType) {
    return expression(() -> builder.emptySet(elementType));
  }

  /**
   * Creates the membership test {@code element \in set}.
   *
   * <p>Example TLA+: {@code x \in S}.</p>
   *
   * @param element the element expression
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr in(TlaBuilderExpr element, TlaBuilderExpr set) {
    return expression(() -> builder.in(state(element), state(set)));
  }

  /**
   * Creates the non-membership test {@code element \notin set}.
   *
   * <p>Example TLA+: {@code x \notin S}.</p>
   *
   * @param element the element expression
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr notIn(TlaBuilderExpr element, TlaBuilderExpr set) {
    return expression(() -> builder.notin(state(element), state(set)));
  }

  /**
   * Creates the intersection of two sets.
   *
   * <p>Example TLA+: {@code A \intersect B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr intersect(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.cap(state(lhs), state(rhs)));
  }

  /**
   * Creates the union of two sets.
   *
   * <p>Example TLA+: {@code A \u005Cunion B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr union(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.cup(state(lhs), state(rhs)));
  }

  /**
   * Creates the union of all sets contained in a set of sets.
   *
   * <p>Example TLA+: {@code \u005CUNION Sets}.</p>
   *
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr unionAll(TlaBuilderExpr set) {
    return expression(() -> builder.union(state(set)));
  }

  /**
   * Creates a set filter containing the members for which the predicate holds.
   *
   * <p>Example TLA+: {@code {x \in S: P(x)}}.</p>
   *
   * @param name the bound-name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr filter(
      TlaBuilderExpr name, TlaBuilderExpr set, TlaBuilderExpr predicate) {
    return expression(() -> builder.filter(state(name), state(set), state(predicate)));
  }

  /**
   * Creates a set comprehension over one or more name/domain bindings.
   *
   * <p>Example TLA+: {@code {x + 1: x \in S}}.</p>
   *
   * @param expression the expression
   * @param bindings one or more bound-name/domain-set pairs
   * @return the pending expression
   */
  @SafeVarargs
  public final TlaBuilderExpr map(
      TlaBuilderExpr expression, ExpressionPair<TlaBuilderExpr>... bindings) {
    return expression(() -> builder.map(state(expression), pairs(bindings)));
  }

  /**
   * Creates the set of all functions from one set to another.
   *
   * <p>Example TLA+: {@code [S -> T]}.</p>
   *
   * @param fromSet the function domain set
   * @param toSet the function codomain set
   * @return the pending expression
   */
  public TlaBuilderExpr funSet(TlaBuilderExpr fromSet, TlaBuilderExpr toSet) {
    return expression(() -> builder.funSet(state(fromSet), state(toSet)));
  }

  /**
   * Creates the set of records whose fields draw values from the supplied field sets.
   *
   * <p>Example TLA+: {@code [status: {"ready", "done"}]}.</p>
   *
   * @param fields one or more field names paired with sets of permitted values
   * @return the pending expression
   */
  @SafeVarargs
  public final TlaBuilderExpr recordSet(NamedExpression<TlaBuilderExpr>... fields) {
    return expression(() -> builder.recSet(named(fields)));
  }

  /**
   * Creates the set of all finite sequences over the supplied element set.
   *
   * <p>Example TLA+: {@code Seq(S)}.</p>
   *
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr seqSet(TlaBuilderExpr set) {
    return expression(() -> builder.seqSet(state(set)));
  }

  /**
   * Creates the subset test {@code lhs \subseteq rhs}.
   *
   * <p>Example TLA+: {@code A \subseteq B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr subsetEq(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.subseteq(state(lhs), state(rhs)));
  }

  /**
   * Creates the set difference {@code lhs \ rhs}.
   *
   * <p>Example TLA+: {@code A \ B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr difference(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.setminus(state(lhs), state(rhs)));
  }

  /**
   * Creates the Cartesian product of the supplied sets.
   *
   * <p>Example TLA+: {@code A \X B}.</p>
   *
   * @param sets the set expressions
   * @return the pending expression
   */
  public TlaBuilderExpr times(TlaBuilderExpr... sets) {
    return expression(() -> builder.times(expressions(sets)));
  }

  /**
   * Creates the power set {@code SUBSET set}.
   *
   * <p>Example TLA+: {@code SUBSET S}.</p>
   *
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr powerSet(TlaBuilderExpr set) {
    return expression(() -> builder.powSet(state(set)));
  }

  /**
   * Tests whether a set is finite.
   *
   * <p>Example TLA+: {@code IsFiniteSet(S)}.</p>
   *
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr isFiniteSet(TlaBuilderExpr set) {
    return expression(() -> builder.isFiniteSet(state(set)));
  }

  /**
   * Creates the cardinality of a finite set.
   *
   * <p>Example TLA+: {@code Cardinality(S)}.</p>
   *
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr cardinality(TlaBuilderExpr set) {
    return expression(() -> builder.cardinality(state(set)));
  }

  /**
   * Creates a closed row-typed record from named field values.
   *
   * <p>Example TLA+: {@code [name |-> "Ada", active |-> TRUE]}.</p>
   *
   * @param fields the field definitions
   * @return the pending expression
   */
  @SafeVarargs
  public final TlaBuilderExpr record(NamedExpression<TlaBuilderExpr>... fields) {
    return expression(
        () -> builder.rowRec(JavaFacadeSupport$.MODULE$.noRowVariable(), named(fields)));
  }

  /**
   * Creates a heterogeneous TLA+ tuple.
   *
   * <p>Example TLA+: {@code <<1, "ready">>}.</p>
   *
   * @param arguments the argument expressions
   * @return the pending expression
   */
  public TlaBuilderExpr tuple(TlaBuilderExpr... arguments) {
    return expression(() -> builder.tuple(expressions(arguments)));
  }

  /**
   * Creates an empty sequence with an explicit element type.
   *
   * <p>Example TLA+: {@code <<>>}.</p>
   *
   * @param elementType the element type
   * @return the pending expression
   */
  public TlaBuilderExpr emptySeq(TlaType1 elementType) {
    return expression(() -> builder.emptySeq(elementType));
  }

  /**
   * Creates a nonempty sequence whose elements all have the same type.
   *
   * <p>Example TLA+: {@code <<1, 2, 3>>}.</p>
   *
   * @param arguments the argument expressions
   * @return the pending expression
   */
  public TlaBuilderExpr seq(TlaBuilderExpr... arguments) {
    return expression(() -> builder.seq(expressions(arguments)));
  }

  /**
   * Creates a function definition over one or more name/domain bindings.
   *
   * <p>Example TLA+: {@code [x \in S |-> x + 1]}.</p>
   *
   * @param body the operator body
   * @param bindings one or more bound-name/domain-set pairs
   * @return the pending expression
   */
  @SafeVarargs
  public final TlaBuilderExpr funDef(
      TlaBuilderExpr body, ExpressionPair<TlaBuilderExpr>... bindings) {
    return expression(() -> builder.funDef(state(body), pairs(bindings)));
  }

  /**
   * Applies a function to an argument.
   *
   * <p>Example TLA+: {@code f[x]}.</p>
   *
   * @param function the function expression
   * @param argument the argument expression
   * @return the pending expression
   */
  public TlaBuilderExpr funApply(TlaBuilderExpr function, TlaBuilderExpr argument) {
    return expression(() -> builder.app(state(function), state(argument)));
  }

  /**
   * Creates the domain of a function.
   *
   * <p>Example TLA+: {@code DOMAIN f}.</p>
   *
   * @param function the function expression
   * @return the pending expression
   */
  public TlaBuilderExpr domain(TlaBuilderExpr function) {
    return expression(() -> builder.dom(state(function)));
  }

  /**
   * Creates a function with one entry replaced by a TLA+ {@code EXCEPT} update.
   *
   * <p>Example TLA+: {@code [f EXCEPT ![x] = 0]}.</p>
   *
   * @param function the function expression
   * @param index the updated index
   * @param value the value expression
   * @return the pending expression
   */
  public TlaBuilderExpr except(
      TlaBuilderExpr function, TlaBuilderExpr index, TlaBuilderExpr value) {
    return expression(() -> builder.except(state(function), state(index), state(value)));
  }

  /**
   * Creates a sequence with an element appended at the end.
   *
   * <p>Example TLA+: {@code Append(sequence, value)}.</p>
   *
   * @param sequence the sequence expression
   * @param element the element expression
   * @return the pending expression
   */
  public TlaBuilderExpr append(TlaBuilderExpr sequence, TlaBuilderExpr element) {
    return expression(() -> builder.append(state(sequence), state(element)));
  }

  /**
   * Creates the concatenation of two sequences.
   *
   * <p>Example TLA+: {@code left \o right}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr concat(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.concat(state(lhs), state(rhs)));
  }

  /**
   * Creates the first element of a sequence.
   *
   * <p>Example TLA+: {@code Head(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the pending expression
   */
  public TlaBuilderExpr head(TlaBuilderExpr sequence) {
    return expression(() -> builder.head(state(sequence)));
  }

  /**
   * Creates the sequence obtained by removing its first element.
   *
   * <p>Example TLA+: {@code Tail(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the pending expression
   */
  public TlaBuilderExpr tail(TlaBuilderExpr sequence) {
    return expression(() -> builder.tail(state(sequence)));
  }

  /**
   * Creates the length of a sequence.
   *
   * <p>Example TLA+: {@code Len(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the pending expression
   */
  public TlaBuilderExpr len(TlaBuilderExpr sequence) {
    return expression(() -> builder.len(state(sequence)));
  }

  /**
   * Creates the inclusive subsequence between two one-based indices.
   *
   * <p>Example TLA+: {@code SubSeq(sequence, 2, 4)}.</p>
   *
   * @param sequence the sequence expression
   * @param fromIndex the inclusive one-based start index
   * @param toIndex the inclusive one-based end index
   * @return the pending expression
   */
  public TlaBuilderExpr subSeq(
      TlaBuilderExpr sequence, TlaBuilderExpr fromIndex, TlaBuilderExpr toIndex) {
    return expression(() -> builder.subseq(state(sequence), state(fromIndex), state(toIndex)));
  }

  /**
   * Creates the primed action expression {@code expression'}.
   *
   * <p>Example TLA+: {@code counter'}.</p>
   *
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr prime(TlaBuilderExpr expression) {
    return expression(() -> builder.prime(state(expression)));
  }

  /**
   * Creates the stuttering action {@code [action]_expression}.
   *
   * <p>Example TLA+: {@code [Next]_vars}.</p>
   *
   * @param action the action expression
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr stutter(TlaBuilderExpr action, TlaBuilderExpr expression) {
    return expression(() -> builder.stutt(state(action), state(expression)));
  }

  /**
   * Creates the non-stuttering action {@code <action>_expression}.
   *
   * <p>Example TLA+: {@code <Next>_vars}.</p>
   *
   * @param action the action expression
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr noStutter(TlaBuilderExpr action, TlaBuilderExpr expression) {
    return expression(() -> builder.nostutt(state(action), state(expression)));
  }

  /**
   * Creates {@code ENABLED action}.
   *
   * <p>Example TLA+: {@code ENABLED Next}.</p>
   *
   * @param action the action expression
   * @return the pending expression
   */
  public TlaBuilderExpr enabled(TlaBuilderExpr action) {
    return expression(() -> builder.enabled(state(action)));
  }

  /**
   * Creates {@code UNCHANGED expression}.
   *
   * <p>Example TLA+: {@code UNCHANGED vars}.</p>
   *
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr unchanged(TlaBuilderExpr expression) {
    return expression(() -> builder.unchanged(state(expression)));
  }

  /**
   * Creates the action composition of {@code lhs} followed by {@code rhs}.
   *
   * <p>Example TLA+: {@code First \cdot Second}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr actionThen(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.comp(state(lhs), state(rhs)));
  }

  /**
   * Creates a TLA+ {@code IF ... THEN ... ELSE ...} expression.
   *
   * <p>Example TLA+: {@code IF condition THEN yes ELSE no}.</p>
   *
   * @param predicate the predicate expression
   * @param whenTrue the expression selected when the predicate is true
   * @param whenFalse the expression selected when the predicate is false
   * @return the pending expression
   */
  public TlaBuilderExpr ite(
      TlaBuilderExpr predicate, TlaBuilderExpr whenTrue, TlaBuilderExpr whenFalse) {
    return expression(() -> builder.ite(state(predicate), state(whenTrue), state(whenFalse)));
  }

  /**
   * Creates a TLA+ {@code CASE} expression with no {@code OTHER} branch.
   *
   * <p>Example TLA+: {@code CASE P -> x [] Q -> y}.</p>
   *
   * @param cases one or more condition/result pairs
   * @return the pending expression
   */
  @SafeVarargs
  public final TlaBuilderExpr caseSplit(ExpressionPair<TlaBuilderExpr>... cases) {
    return expression(() -> builder.caseSplit(pairs(cases)));
  }

  /**
   * Creates a TLA+ {@code CASE} expression with an {@code OTHER} result.
   *
   * <p>Example TLA+: {@code CASE P -> x [] OTHER -> y}.</p>
   *
   * @param other the result used when no condition holds
   * @param cases one or more condition/result pairs
   * @return the pending expression
   */
  @SafeVarargs
  public final TlaBuilderExpr caseOther(
      TlaBuilderExpr other, ExpressionPair<TlaBuilderExpr>... cases) {
    return expression(() -> builder.caseOther(state(other), pairs(cases)));
  }

  /**
   * Creates the temporal formula {@code []predicate} (always).
   *
   * <p>Example TLA+: {@code []P}.</p>
   *
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr always(TlaBuilderExpr predicate) {
    return expression(() -> builder.box(state(predicate)));
  }

  /**
   * Creates the temporal formula {@code <>predicate} (eventually).
   *
   * <p>Example TLA+: {@code <>P}.</p>
   *
   * @param predicate the predicate expression
   * @return the pending expression
   */
  public TlaBuilderExpr eventually(TlaBuilderExpr predicate) {
    return expression(() -> builder.diamond(state(predicate)));
  }

  /**
   * Creates the temporal leads-to formula {@code lhs ~> rhs}.
   *
   * <p>Example TLA+: {@code P ~> Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr leadsTo(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.leadsTo(state(lhs), state(rhs)));
  }

  /**
   * Creates the temporal guarantees formula {@code lhs -+-> rhs}.
   *
   * <p>Example TLA+: {@code P -+-> Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the pending expression
   */
  public TlaBuilderExpr guarantees(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.guarantees(state(lhs), state(rhs)));
  }

  /**
   * Creates the weak-fairness condition for an action over the supplied variables.
   *
   * <p>Example TLA+: {@code WF_vars(Next)}.</p>
   *
   * @param variables the state variables
   * @param action the action expression
   * @return the pending expression
   */
  public TlaBuilderExpr weakFair(TlaBuilderExpr variables, TlaBuilderExpr action) {
    return expression(() -> builder.WF(state(variables), state(action)));
  }

  /**
   * Creates the strong-fairness condition for an action over the supplied variables.
   *
   * <p>Example TLA+: {@code SF_vars(Next)}.</p>
   *
   * @param variables the state variables
   * @param action the action expression
   * @return the pending expression
   */
  public TlaBuilderExpr strongFair(TlaBuilderExpr variables, TlaBuilderExpr action) {
    return expression(() -> builder.SF(state(variables), state(action)));
  }

  /**
   * Creates temporal existential quantification over a variable.
   *
   * <p>Example TLA+: {@code \EE x: P(x)}.</p>
   *
   * @param variable the bound variable expression
   * @param formula the temporal formula
   * @return the pending expression
   */
  public TlaBuilderExpr temporalExists(TlaBuilderExpr variable, TlaBuilderExpr formula) {
    return expression(() -> builder.EE(state(variable), state(formula)));
  }

  /**
   * Creates temporal universal quantification over a variable.
   *
   * <p>Example TLA+: {@code \AA x: P(x)}.</p>
   *
   * @param variable the bound variable expression
   * @param formula the temporal formula
   * @return the pending expression
   */
  public TlaBuilderExpr temporalForAll(TlaBuilderExpr variable, TlaBuilderExpr formula) {
    return expression(() -> builder.AA(state(variable), state(formula)));
  }

  /**
   * Creates the Apalache assignment {@code lhs := rhs}.
   * <p>In strict mode, {@code lhs} must be a primed variable name.</p>
   *
   * <p>Example TLA+: {@code counter' := counter + 1}.</p>
   *
   * @param lhs the primed variable to assign
   * @param rhs the value assigned to the variable
   * @return the pending expression
   */
  public TlaBuilderExpr assign(TlaBuilderExpr lhs, TlaBuilderExpr rhs) {
    return expression(() -> builder.assign(state(lhs), state(rhs)));
  }

  /**
   * Creates an Apalache value generator with an explicit result type.
   * <p>The bound must become a constant expression after preprocessing.</p>
   *
   * <p>Example TLA+: {@code Gen(3)}.</p>
   *
   * @param bound an expression that becomes constant during preprocessing
   * @param returnType the result type
   * @return the pending expression
   */
  public TlaBuilderExpr gen(TlaBuilderExpr bound, TlaType1 returnType) {
    return expression(() -> builder.gen(state(bound), returnType));
  }

  /**
   * Creates an Apalache expression that applies a binary operator repeatedly to an initial value.
   * <p>In strict mode, the count must be positive and the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code Repeat(Inc, 3, 0)}.</p>
   *
   * @param operator the binary operator applied on each iteration
   * @param count the number of applications
   * @param initial the first accumulator value
   * @return the pending expression
   */
  public TlaBuilderExpr repeat(
      TlaBuilderExpr operator, BigInteger count, TlaBuilderExpr initial) {
    return expression(
        () ->
            builder.repeat(
                state(operator), JavaFacadeSupport$.MODULE$.bigInt(count), state(initial)));
  }

  /**
   * Creates an Apalache expression that applies a binary operator repeatedly to an initial value.
   * <p>In strict mode, the count must be positive and the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code Repeat(Inc, 3, 0)}.</p>
   *
   * @param operator the binary operator applied on each iteration
   * @param count the number of applications
   * @param initial the first accumulator value
   * @return the pending expression
   */
  public TlaBuilderExpr repeat(
      TlaBuilderExpr operator, long count, TlaBuilderExpr initial) {
    return repeat(operator, BigInteger.valueOf(count), initial);
  }

  /**
   * Creates Apalache's Skolemization marker for an existential formula.
   * <p>In strict mode, the argument must be an existential quantification.</p>
   *
   * <p>Example TLA+: {@code Skolem(\E x \in S: P(x))}.</p>
   *
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr skolem(TlaBuilderExpr expression) {
    return expression(() -> builder.skolem(state(expression)));
  }

  /**
   * Creates an Apalache expression that chooses an unspecified member of a set.
   *
   * <p>Example TLA+: {@code Guess(S)}.</p>
   *
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr guess(TlaBuilderExpr set) {
    return expression(() -> builder.guess(state(set)));
  }

  /**
   * Marks a power set or function set for explicit expansion by Apalache.
   * <p>Strict mode rejects other expression shapes.</p>
   *
   * <p>Example TLA+: {@code Expand(SUBSET S)}.</p>
   *
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr expand(TlaBuilderExpr expression) {
    return expression(() -> builder.expand(state(expression)));
  }

  /**
   * Marks a constant lower bound on a set's cardinality for Apalache.
   * <p>In strict mode, the argument must have the form {@code Cardinality(set) >= integer}.</p>
   *
   * <p>Example TLA+: {@code ConstCardinality(Cardinality(S) >= 3)}.</p>
   *
   * @param expression the expression
   * @return the pending expression
   */
  public TlaBuilderExpr constCard(TlaBuilderExpr expression) {
    return expression(() -> builder.constCard(state(expression)));
  }

  /**
   * Creates a sequence of a fixed length by applying a unary operator to each index.
   * <p>In strict mode, the length must be nonnegative and the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code MkSeq(3, Elem)}.</p>
   *
   * @param count the sequence length
   * @param operator a unary operator mapping each index to an element
   * @return the pending expression
   */
  public TlaBuilderExpr mkSeq(BigInteger count, TlaBuilderExpr operator) {
    return expression(
        () -> builder.mkSeq(JavaFacadeSupport$.MODULE$.bigInt(count), state(operator)));
  }

  /**
   * Creates a sequence of a fixed length by applying a unary operator to each index.
   * <p>In strict mode, the length must be nonnegative and the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code MkSeq(3, Elem)}.</p>
   *
   * @param count the sequence length
   * @param operator a unary operator mapping each index to an element
   * @return the pending expression
   */
  public TlaBuilderExpr mkSeq(long count, TlaBuilderExpr operator) {
    return mkSeq(BigInteger.valueOf(count), operator);
  }

  /**
   * Creates a sequence whose length is given by a constant expression, using a unary operator for its elements.
   * <p>In strict mode, the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code MkSeq(n, Elem)}.</p>
   *
   * @param count a constant expression for the sequence length
   * @param operator a unary operator mapping each index to an element
   * @return the pending expression
   */
  public TlaBuilderExpr mkSeqConst(TlaBuilderExpr count, TlaBuilderExpr operator) {
    return expression(() -> builder.mkSeqConst(state(count), state(operator)));
  }

  /**
   * Folds a binary operator over a set, starting with an initial value.
   * <p>In strict mode, the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code ApaFoldSet(Add, 0, S)}.</p>
   *
   * @param operator the binary accumulator operator
   * @param initial the initial value
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr foldSet(
      TlaBuilderExpr operator, TlaBuilderExpr initial, TlaBuilderExpr set) {
    return expression(() -> builder.foldSet(state(operator), state(initial), state(set)));
  }

  /**
   * Folds a binary operator over a sequence, starting with an initial value.
   * <p>In strict mode, the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code ApaFoldSeqLeft(Add, 0, sequence)}.</p>
   *
   * @param operator the binary accumulator operator
   * @param initial the initial value
   * @param sequence the sequence expression
   * @return the pending expression
   */
  public TlaBuilderExpr foldSeq(
      TlaBuilderExpr operator, TlaBuilderExpr initial, TlaBuilderExpr sequence) {
    return expression(() -> builder.foldSeq(state(operator), state(initial), state(sequence)));
  }

  /**
   * Treats a set of pairs as a function.
   *
   * <p>Example TLA+: {@code SetAsFun({<<1, "one">>, <<2, "two">>})}.</p>
   *
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr setAsFun(TlaBuilderExpr set) {
    return expression(() -> builder.setAsFun(state(set)));
  }

  /**
   * Creates a typed placeholder that reports an unsupported expression to the model checker.
   *
   * <p>Example TLA+: {@code __NotSupportedByModelChecker("unsupported")}.</p>
   *
   * @param message the diagnostic reported by the model checker
   * @param type the placeholder expression's result type
   * @return the pending expression
   */
  public TlaBuilderExpr notSupportedByModelChecker(String message, TlaType1 type) {
    return expression(() -> builder.notSupportedByModelChecker(message, type));
  }

  /**
   * Creates an internal SMT constraint requiring all arguments to be pairwise distinct.
   *
   * <p>Example TLA+: {@code Distinct(x, y, z)}.</p>
   *
   * @param arguments the argument expressions
   * @return the pending expression
   */
  public TlaBuilderExpr distinct(TlaBuilderExpr... arguments) {
    return expression(() -> builder.distinct(expressions(arguments)));
  }

  /**
   * Creates Apalache's internal capacity value for a sequence.
   *
   * <p>Example TLA+: {@code __ApalacheSeqCapacity(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the pending expression
   */
  public TlaBuilderExpr apalacheSeqCapacity(TlaBuilderExpr sequence) {
    return expression(() -> builder.apalacheSeqCapacity(state(sequence)));
  }

  /**
   * Creates a tagged value of an explicitly supplied variant type.
   *
   * <p>Example TLA+: {@code Variant("Some", 1)}.</p>
   *
   * @param tag the variant tag
   * @param value the value expression
   * @param targetType a variant type containing the supplied tag
   * @return the pending expression
   */
  public TlaBuilderExpr variant(
      String tag, TlaBuilderExpr value, VariantT1 targetType) {
    return expression(() -> builder.variant(tag, state(value), targetType));
  }

  /**
   * Extracts the values with a specified tag from a set of variants.
   *
   * <p>Example TLA+: {@code VariantFilter("Some", variants)}.</p>
   *
   * @param tag the tag whose values are selected
   * @param set the set expression
   * @return the pending expression
   */
  public TlaBuilderExpr variantFilter(String tag, TlaBuilderExpr set) {
    return expression(() -> builder.variantFilter(tag, state(set)));
  }

  /**
   * Creates the string tag of a variant value.
   *
   * <p>Example TLA+: {@code VariantTag(variant)}.</p>
   *
   * @param variant the variant expression
   * @return the pending expression
   */
  public TlaBuilderExpr variantTag(TlaBuilderExpr variant) {
    return expression(() -> builder.variantTag(state(variant)));
  }

  /**
   * Extracts the value for a tag, or returns a fallback when the variant has another tag.
   *
   * <p>Example TLA+: {@code VariantGetOrElse("Some", variant, 0)}.</p>
   *
   * @param tag the tag whose value is requested
   * @param variant the variant expression
   * @param defaultValue the fallback value
   * @return the pending expression
   */
  public TlaBuilderExpr variantGetOrElse(
      String tag, TlaBuilderExpr variant, TlaBuilderExpr defaultValue) {
    return expression(
        () -> builder.variantGetOrElse(tag, state(variant), state(defaultValue)));
  }

  /**
   * Extracts the value for a tag, assuming the variant has that tag.
   *
   * <p>Use {@code variantGetOrElse} when the variant may contain a different tag.</p>
   *
   * <p>Example TLA+: {@code VariantGetUnsafe("Some", variant)}.</p>
   *
   * @param tag the tag whose value is requested
   * @param variant the variant expression
   * @return the pending expression
   */
  public TlaBuilderExpr variantGetUnsafe(String tag, TlaBuilderExpr variant) {
    return expression(() -> builder.variantGetUnsafe(tag, state(variant)));
  }

  /**
   * Retrieves the underlying builder instruction from a pending expression.
   *
   * @param expression the pending expression
   * @return the underlying expression instruction
   */
  private IndexedStateT state(TlaBuilderExpr expression) {
    return JavaFacadeSupport$.MODULE$.checkedState(expression.state());
  }

  /**
   * Retrieves the underlying builder instruction from a pending declaration.
   *
   * @param declaration the pending declaration
   * @return the underlying declaration instruction
   */
  private IndexedStateT declState(TlaBuilderDecl declaration) {
    return JavaFacadeSupport$.MODULE$.checkedDeclState(declaration.state());
  }

  /**
   * Converts pending expressions to the collection expected by the underlying builder.
   *
   * @param expressions the pending expressions
   * @return the underlying expression instructions
   */
  private Seq expressions(TlaBuilderExpr[] expressions) {
    return JavaFacadeSupport$.MODULE$.checkedExpressions(expressions, TlaBuilderExpr::state);
  }

  /**
   * Converts expression-pair arguments to the collection expected by the underlying builder.
   *
   * @param pairs the expression pairs to convert
   * @return the underlying expression pairs
   */
  private Seq pairs(ExpressionPair<TlaBuilderExpr>[] pairs) {
    return JavaFacadeSupport$.MODULE$.checkedPairs(pairs, TlaBuilderExpr::state);
  }

  /**
   * Converts named-expression arguments to the collection expected by the underlying builder.
   *
   * @param fields the field definitions
   * @return the underlying named expressions
   */
  private Seq named(NamedExpression<TlaBuilderExpr>[] fields) {
    return JavaFacadeSupport$.MODULE$.checkedNamed(fields, TlaBuilderExpr::state);
  }

  /**
   * Runs an underlying builder action and maps failures to public facade exceptions.
   *
   * @param action the underlying builder action
   * @param <T> the action result type
   * @return the action result
   */
  private static <T> T call(Callable<T> action) {
    try {
      return action.call();
    } catch (Exception exception) {
      throw JavaFacadeSupport$.MODULE$.translateException(exception);
    }
  }

  /**
   * Wraps an expression-building computation in a pending expression.
   *
   * @param action the underlying builder computation
   * @return the pending expression
   */
  private TlaBuilderExpr expression(Callable<?> action) {
    return new TlaBuilderExpr(call(action));
  }

  /**
   * Wraps a declaration-building computation in a pending declaration.
   *
   * @param action the underlying builder computation
   * @return the pending operator declaration
   */
  private TlaBuilderDecl declaration(Callable<?> action) {
    return new TlaBuilderDecl(call(action));
  }
}
