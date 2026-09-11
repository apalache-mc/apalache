package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.ConstT1;
import at.forsyte.apalache.tla.lir.TlaEx;
import at.forsyte.apalache.tla.lir.TlaOperDecl;
import at.forsyte.apalache.tla.lir.TlaType1;
import at.forsyte.apalache.tla.lir.TlaVarDecl;
import at.forsyte.apalache.tla.lir.VariantT1;
import at.forsyte.apalache.tla.typecomp.ScopeUnsafeBuilder;
import java.math.BigInteger;
import java.util.concurrent.Callable;
import org.apalache_mc.tla.jir.impl.JavaToScalaAdapter$;
import scala.collection.immutable.Seq;

/**
 * Builds typed TLA+ IR without tracking lexical scope.
 *
 * <p>Operations return {@code TlaEx} or {@code TlaOperDecl} values immediately and still reject incompatible operand
 * types. The builder does not detect unknown names, inconsistent uses of a name, or shadowing. It is intended for code
 * that already owns scope validation, such as transformations of existing IR. Prefer {@link TlaCheckedBuilder} when
 * constructing new expressions from names.</p>
 */
@SuppressWarnings({"rawtypes", "unchecked", "unused"})
public final class TlaTypedScopeUncheckedBuilder {
  private final ScopeUnsafeBuilder builder;

  /**
   * Creates a builder that enforces type and operation-specific structural requirements.
   */
  public TlaTypedScopeUncheckedBuilder() {
    this(true);
  }

  /**
   * Creates a builder and selects whether Apalache-specific structural requirements are enforced.
   *
   * <p>Type checking remains enabled in both modes, and scope checking remains disabled. Strict mode additionally
   * checks requirements that are not expressible in TLA+ types, such as requiring {@code assign}'s left side to be a
   * primed variable.</p>
   *
   * @param strict {@code true} to enable the additional structural checks on Apalache-specific operations;
   *     {@code false} to omit those additional checks
   */
  public TlaTypedScopeUncheckedBuilder(boolean strict) {
    builder = new ScopeUnsafeBuilder(strict);
  }

  /**
   * Returns an existing typed IR expression unchanged.
   *
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx unchecked(TlaEx expression) {
    return expression(() -> builder.unchecked(expression));
  }

  /**
   * Returns an existing typed IR operator declaration unchanged.
   *
   * @param declaration the declaration
   * @return the typed TLA+ IR operator declaration
   */
  public TlaOperDecl uncheckedDecl(TlaOperDecl declaration) {
    return declaration(() -> builder.uncheckedDecl(declaration));
  }

  /**
   * Creates an integer literal.
   *
   * <p>Example TLA+: {@code 42}.</p>
   *
   * @param value the value
   * @return the typed TLA+ IR expression
   */
  public TlaEx integer(BigInteger value) {
    return expression(
        () -> JavaToScalaAdapter$.MODULE$.uncheckedInteger(
            builder, JavaToScalaAdapter$.MODULE$.bigInt(value)));
  }

  /**
   * Creates an integer literal.
   *
   * <p>Example TLA+: {@code 42}.</p>
   *
   * @param value the value
   * @return the typed TLA+ IR expression
   */
  public TlaEx integer(long value) {
    return integer(BigInteger.valueOf(value));
  }

  /**
   * Creates a TLA+ string literal.
   *
   * <p>Example TLA+: {@code "ready"}.</p>
   *
   * @param value the value
   * @return the typed TLA+ IR expression
   */
  public TlaEx str(String value) {
    return expression(() -> builder.str(value));
  }

  /**
   * Creates a Boolean literal.
   *
   * <p>Example TLA+: {@code TRUE}.</p>
   *
   * @param value the value
   * @return the typed TLA+ IR expression
   */
  public TlaEx bool(boolean value) {
    return expression(() -> builder.bool(value));
  }

  /**
   * Creates a model value from a root name and an uninterpreted constant type.
   *
   * <p>Example TLA+: {@code red_OF_Color}.</p>
   *
   * @param root the model-value root, without an {@code _OF_} suffix
   * @param type the model value's uninterpreted constant type
   * @return the typed TLA+ IR expression
   */
  public TlaEx constant(String root, ConstT1 type) {
    return expression(() -> JavaToScalaAdapter$.MODULE$.uncheckedConstant(builder, root, type));
  }

  /**
   * Creates a model value from its encoded name, such as {@code 1_OF_Process}.
   *
   * <p>Example TLA+: {@code red_OF_Color}.</p>
   *
   * @param value the complete encoded model-value name
   * @return the typed TLA+ IR expression
   */
  public TlaEx constParsed(String value) {
    return expression(() -> builder.constParsed(value));
  }

  /**
   * Creates the built-in TLA+ set {@code BOOLEAN}.
   *
   * <p>Example TLA+: {@code BOOLEAN}.</p>
   *
   * @return the typed TLA+ IR expression
   */
  public TlaEx booleanSet() {
    return expression(builder::booleanSet);
  }

  /**
   * Creates the built-in TLA+ set {@code STRING}.
   *
   * <p>Example TLA+: {@code STRING}.</p>
   *
   * @return the typed TLA+ IR expression
   */
  public TlaEx stringSet() {
    return expression(builder::stringSet);
  }

  /**
   * Creates the built-in TLA+ set {@code Int}.
   *
   * <p>Example TLA+: {@code Int}.</p>
   *
   * @return the typed TLA+ IR expression
   */
  public TlaEx intSet() {
    return expression(builder::intSet);
  }

  /**
   * Creates the built-in TLA+ set {@code Nat}.
   *
   * <p>Example TLA+: {@code Nat}.</p>
   *
   * @return the typed TLA+ IR expression
   */
  public TlaEx natSet() {
    return expression(builder::natSet);
  }

  /**
   * Creates a reference to a TLA+ name with an explicit type.
   *
   * <p>Example TLA+: {@code counter}.</p>
   *
   * @param name the referenced TLA+ name
   * @param type the type assigned to that name
   * @return the typed TLA+ IR expression
   */
  public TlaEx name(String name, TlaType1 type) {
    return expression(() -> builder.name(name, type));
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
   * @return the typed TLA+ IR operator declaration
   */
  public TlaOperDecl decl(String name, TlaEx body, TypedParameter... parameters) {
    return declaration(
        () -> builder.decl(name, body, JavaToScalaAdapter$.MODULE$.typedParameters(parameters)));
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
   * @return the typed TLA+ IR expression
   */
  public TlaEx lambda(String uniqueName, TlaEx body, TypedParameter... parameters) {
    return expression(
        () -> builder.lambda(
            uniqueName, body, JavaToScalaAdapter$.MODULE$.typedParameters(parameters)));
  }

  /**
   * Creates a TLA+ {@code LET ... IN ...} expression containing the supplied local declarations.
   *
   * <p>Example TLA+: {@code LET Inc(x) == x + 1 IN Inc(2)}.</p>
   *
   * @param body the expression evaluated with the local declarations in scope
   * @param declarations one or more local operator declarations
   * @return the typed TLA+ IR expression
   */
  public TlaEx letIn(TlaEx body, TlaOperDecl... declarations) {
    return expression(
        () -> builder.letIn(body, JavaToScalaAdapter$.MODULE$.uncheckedDecls(declarations)));
  }

  /**
   * Creates nested TLA+ {@code EXCEPT} updates, applying the supplied replacements from left to right.
   *
   * <p>Example TLA+: {@code [f EXCEPT ![1] = 10, ![2] = 20]}.</p>
   *
   * @param function the function expression
   * @param updates one or more index/replacement pairs, applied in order
   * @return the typed TLA+ IR expression
   */
  @SafeVarargs
  public final TlaEx exceptMany(TlaEx function, ExceptUpdate<TlaEx>... updates) {
    return expression(
        () -> builder.exceptMany(function, JavaToScalaAdapter$.MODULE$.uncheckedUpdates(updates)));
  }

  /**
   * Creates a name reference using the name and type of an existing variable declaration.
   *
   * <p>Example TLA+: {@code counter}.</p>
   *
   * @param declaration the declaration
   * @return the typed TLA+ IR expression
   */
  public TlaEx varDeclAsNameEx(TlaVarDecl declaration) {
    return expression(() -> builder.varDeclAsNameEx(declaration));
  }

  /**
   * Creates the action formula {@code lhs' = rhs}.
   *
   * <p>Example TLA+: {@code counter' = counter + 1}.</p>
   *
   * @param lhs the unprimed left-hand expression
   * @param rhs the value compared with the primed left-hand expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx primeEq(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.primeEq(lhs, rhs));
  }

  /**
   * Creates the equality comparison {@code lhs = rhs}.
   *
   * <p>Example TLA+: {@code x = y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx eql(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.eql(lhs, rhs));
  }

  /**
   * Creates the inequality comparison {@code lhs /= rhs}.
   *
   * <p>Example TLA+: {@code x /= y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx neql(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.neql(lhs, rhs));
  }

  /**
   * Applies an operator value to zero or more arguments.
   *
   * <p>Example TLA+: {@code Max(x, y)}.</p>
   *
   * @param operator an operator-valued expression
   * @param arguments the argument expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx operApply(TlaEx operator, TlaEx... arguments) {
    return expression(() -> builder.appOp(operator, expressions(arguments)));
  }

  /**
   * Creates the unbounded choice {@code CHOOSE name : predicate}.
   *
   * <p>Example TLA+: {@code CHOOSE x: P(x)}.</p>
   *
   * @param name the bound name expression
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx choose(TlaEx name, TlaEx predicate) {
    return expression(() -> builder.choose(name, predicate));
  }

  /**
   * Creates the bounded choice {@code CHOOSE name \in set : predicate}.
   *
   * <p>Example TLA+: {@code CHOOSE x \in S: P(x)}.</p>
   *
   * @param name the bound name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx choose(TlaEx name, TlaEx set, TlaEx predicate) {
    return expression(() -> builder.choose(name, set, predicate));
  }

  /**
   * Attaches a TLA+ label and its string arguments to an expression.
   *
   * <p>Example TLA+: {@code Step(i):: counter' = counter + 1}.</p>
   *
   * @param expression the expression
   * @param arguments one or more string components of the label
   * @return the typed TLA+ IR expression
   */
  public TlaEx label(TlaEx expression, String... arguments) {
    return expression(
        () -> builder.label(expression, JavaToScalaAdapter$.MODULE$.strings(arguments)));
  }

  /**
   * Creates the conjunction of the supplied Boolean expressions.
   *
   * <p>Example TLA+: {@code P /\ Q}.</p>
   *
   * @param arguments the argument expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx and(TlaEx... arguments) {
    return expression(() -> builder.and(expressions(arguments)));
  }

  /**
   * Creates the disjunction of the supplied Boolean expressions.
   *
   * <p>Example TLA+: {@code P \/ Q}.</p>
   *
   * @param arguments the argument expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx or(TlaEx... arguments) {
    return expression(() -> builder.or(expressions(arguments)));
  }

  /**
   * Creates the negation of a Boolean expression.
   *
   * <p>Example TLA+: {@code ~P}.</p>
   *
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx not(TlaEx predicate) {
    return expression(() -> builder.not(predicate));
  }

  /**
   * Creates the Boolean implication {@code lhs => rhs}.
   *
   * <p>Example TLA+: {@code P => Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx implies(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.impl(lhs, rhs));
  }

  /**
   * Creates the Boolean equivalence {@code lhs <=> rhs}.
   *
   * <p>Example TLA+: {@code P <=> Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx equiv(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.equiv(lhs, rhs));
  }

  /**
   * Creates universal quantification with the name bounded by a set.
   *
   * <p>Example TLA+: {@code \A x \in S: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx forall(TlaEx name, TlaEx set, TlaEx predicate) {
    return expression(() -> builder.forall(name, set, predicate));
  }

  /**
   * Creates unbounded universal quantification over a name.
   *
   * <p>Example TLA+: {@code \A x: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx forall(TlaEx name, TlaEx predicate) {
    return expression(() -> builder.forall(name, predicate));
  }

  /**
   * Creates existential quantification with the name bounded by a set.
   *
   * <p>Example TLA+: {@code \E x \in S: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx exists(TlaEx name, TlaEx set, TlaEx predicate) {
    return expression(() -> builder.exists(name, set, predicate));
  }

  /**
   * Creates unbounded existential quantification over a name.
   *
   * <p>Example TLA+: {@code \E x: P(x)}.</p>
   *
   * @param name the bound-name expression
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx exists(TlaEx name, TlaEx predicate) {
    return expression(() -> builder.exists(name, predicate));
  }

  /**
   * Creates integer addition {@code lhs + rhs}.
   *
   * <p>Example TLA+: {@code x + y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx plus(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.plus(lhs, rhs));
  }

  /**
   * Creates integer subtraction {@code lhs - rhs}.
   *
   * <p>Example TLA+: {@code x - y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx minus(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.minus(lhs, rhs));
  }

  /**
   * Creates integer negation {@code -value}.
   *
   * <p>Example TLA+: {@code -x}.</p>
   *
   * @param value the value expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx uminus(TlaEx value) {
    return expression(() -> builder.uminus(value));
  }

  /**
   * Creates integer multiplication {@code lhs * rhs}.
   *
   * <p>Example TLA+: {@code x * y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx mult(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.mult(lhs, rhs));
  }

  /**
   * Creates integer division {@code lhs \div rhs}.
   *
   * <p>Example TLA+: {@code x \div y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx div(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.div(lhs, rhs));
  }

  /**
   * Creates the integer remainder {@code lhs % rhs}.
   *
   * <p>Example TLA+: {@code x % y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx mod(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.mod(lhs, rhs));
  }

  /**
   * Creates integer exponentiation {@code lhs ^ rhs}.
   *
   * <p>Example TLA+: {@code x ^ y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx exp(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.exp(lhs, rhs));
  }

  /**
   * Creates the inclusive integer interval {@code lhs .. rhs}.
   *
   * <p>Example TLA+: {@code 1 .. 10}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx interval(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.dotdot(lhs, rhs));
  }

  /**
   * Creates the integer comparison {@code lhs < rhs}.
   *
   * <p>Example TLA+: {@code x < y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx lt(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.lt(lhs, rhs));
  }

  /**
   * Creates the integer comparison {@code lhs > rhs}.
   *
   * <p>Example TLA+: {@code x > y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx gt(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.gt(lhs, rhs));
  }

  /**
   * Creates the integer comparison {@code lhs <= rhs}.
   *
   * <p>Example TLA+: {@code x <= y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx le(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.le(lhs, rhs));
  }

  /**
   * Creates the integer comparison {@code lhs >= rhs}.
   *
   * <p>Example TLA+: {@code x >= y}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx ge(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.ge(lhs, rhs));
  }

  /**
   * Creates an explicitly enumerated set from the supplied elements.
   *
   * <p>Example TLA+: {@code {1, 2, 3}}.</p>
   *
   * @param arguments the argument expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx enumSet(TlaEx... arguments) {
    return expression(() -> builder.enumSet(expressions(arguments)));
  }

  /**
   * Creates an empty set with an explicit element type.
   *
   * <p>Example TLA+: {@code {}}.</p>
   *
   * @param elementType the element type
   * @return the typed TLA+ IR expression
   */
  public TlaEx emptySet(TlaType1 elementType) {
    return expression(() -> builder.emptySet(elementType));
  }

  /**
   * Creates the membership test {@code element \in set}.
   *
   * <p>Example TLA+: {@code x \in S}.</p>
   *
   * @param element the element expression
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx in(TlaEx element, TlaEx set) {
    return expression(() -> builder.in(element, set));
  }

  /**
   * Creates the non-membership test {@code element \notin set}.
   *
   * <p>Example TLA+: {@code x \notin S}.</p>
   *
   * @param element the element expression
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx notIn(TlaEx element, TlaEx set) {
    return expression(() -> builder.notin(element, set));
  }

  /**
   * Creates the intersection of two sets.
   *
   * <p>Example TLA+: {@code A \cap B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx intersect(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.cap(lhs, rhs));
  }

  /**
   * Creates the union of two sets.
   *
   * <p>Example TLA+: {@code A \cup B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx union(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.cup(lhs, rhs));
  }

  /**
   * Creates the union of all sets contained in a set of sets.
   *
   * <p>Example TLA+: {@code UNION Sets}.</p>
   *
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx unionAll(TlaEx set) {
    return expression(() -> builder.union(set));
  }

  /**
   * Creates a set filter containing the members for which the predicate holds.
   *
   * <p>Example TLA+: {@code {x \in S: P(x)}}.</p>
   *
   * @param name the bound-name expression
   * @param set the set expression
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx filter(TlaEx name, TlaEx set, TlaEx predicate) {
    return expression(() -> builder.filter(name, set, predicate));
  }

  /**
   * Creates a set comprehension over one or more name/domain bindings.
   *
   * <p>Example TLA+: {@code {x + 1: x \in S}}.</p>
   *
   * @param expression the expression
   * @param bindings one or more bound-name/domain-set pairs
   * @return the typed TLA+ IR expression
   */
  @SafeVarargs
  public final TlaEx map(TlaEx expression, ExpressionPair<TlaEx>... bindings) {
    return expression(() -> builder.map(expression, pairs(bindings)));
  }

  /**
   * Creates the set of all functions from one set to another.
   *
   * <p>Example TLA+: {@code [S -> T]}.</p>
   *
   * @param fromSet the function domain set
   * @param toSet the function codomain set
   * @return the typed TLA+ IR expression
   */
  public TlaEx funSet(TlaEx fromSet, TlaEx toSet) {
    return expression(() -> builder.funSet(fromSet, toSet));
  }

  /**
   * Creates the set of records whose fields draw values from the supplied field sets.
   *
   * <p>Example TLA+: {@code [status: {"ready", "done"}]}.</p>
   *
   * @param fields one or more field names paired with sets of permitted values
   * @return the typed TLA+ IR expression
   */
  @SafeVarargs
  public final TlaEx recordSet(NamedExpression<TlaEx>... fields) {
    return expression(() -> builder.recSet(named(fields)));
  }

  /**
   * Creates the set of all finite sequences over the supplied element set.
   *
   * <p>Example TLA+: {@code Seq(S)}.</p>
   *
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx seqSet(TlaEx set) {
    return expression(() -> builder.seqSet(set));
  }

  /**
   * Creates the subset test {@code lhs \subseteq rhs}.
   *
   * <p>Example TLA+: {@code A \subseteq B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx subsetEq(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.subseteq(lhs, rhs));
  }

  /**
   * Creates the set difference {@code lhs \ rhs}.
   *
   * <p>Example TLA+: {@code A \ B}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx difference(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.setminus(lhs, rhs));
  }

  /**
   * Creates the Cartesian product of the supplied sets.
   *
   * <p>Example TLA+: {@code A \X B}.</p>
   *
   * @param sets the set expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx times(TlaEx... sets) {
    return expression(() -> builder.times(expressions(sets)));
  }

  /**
   * Creates the power set {@code SUBSET set}.
   *
   * <p>Example TLA+: {@code SUBSET S}.</p>
   *
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx powerSet(TlaEx set) {
    return expression(() -> builder.powSet(set));
  }

  /**
   * Tests whether a set is finite.
   *
   * <p>Example TLA+: {@code IsFiniteSet(S)}.</p>
   *
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx isFiniteSet(TlaEx set) {
    return expression(() -> builder.isFiniteSet(set));
  }

  /**
   * Creates the cardinality of a finite set.
   *
   * <p>Example TLA+: {@code Cardinality(S)}.</p>
   *
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx cardinality(TlaEx set) {
    return expression(() -> builder.cardinality(set));
  }

  /**
   * Creates a closed row-typed record from named field values.
   *
   * <p>Example TLA+: {@code [name |-> "Ada", active |-> TRUE]}.</p>
   *
   * @param fields the field definitions
   * @return the typed TLA+ IR expression
   */
  @SafeVarargs
  public final TlaEx record(NamedExpression<TlaEx>... fields) {
    return expression(
        () -> builder.rowRec(JavaToScalaAdapter$.MODULE$.noUncheckedRowVariable(), named(fields)));
  }

  /**
   * Creates a heterogeneous TLA+ tuple.
   *
   * <p>Example TLA+: {@code <<1, "ready">>}.</p>
   *
   * @param arguments the argument expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx tuple(TlaEx... arguments) {
    return expression(() -> builder.tuple(expressions(arguments)));
  }

  /**
   * Creates an empty sequence with an explicit element type.
   *
   * <p>Example TLA+: {@code <<>>}.</p>
   *
   * @param elementType the element type
   * @return the typed TLA+ IR expression
   */
  public TlaEx emptySeq(TlaType1 elementType) {
    return expression(() -> builder.emptySeq(elementType));
  }

  /**
   * Creates a nonempty sequence whose elements all have the same type.
   *
   * <p>Example TLA+: {@code <<1, 2, 3>>}.</p>
   *
   * @param arguments the argument expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx seq(TlaEx... arguments) {
    return expression(() -> builder.seq(expressions(arguments)));
  }

  /**
   * Creates a function definition over one or more name/domain bindings.
   *
   * <p>Example TLA+: {@code [x \in S |-> x + 1]}.</p>
   *
   * @param body the operator body
   * @param bindings one or more bound-name/domain-set pairs
   * @return the typed TLA+ IR expression
   */
  @SafeVarargs
  public final TlaEx funDef(TlaEx body, ExpressionPair<TlaEx>... bindings) {
    return expression(() -> builder.funDef(body, pairs(bindings)));
  }

  /**
   * Applies a function to an argument.
   *
   * <p>Example TLA+: {@code f[x]}.</p>
   *
   * @param function the function expression
   * @param argument the argument expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx funApply(TlaEx function, TlaEx argument) {
    return expression(() -> builder.app(function, argument));
  }

  /**
   * Creates the domain of a function.
   *
   * <p>Example TLA+: {@code DOMAIN f}.</p>
   *
   * @param function the function expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx domain(TlaEx function) {
    return expression(() -> builder.dom(function));
  }

  /**
   * Creates a function with one entry replaced by a TLA+ {@code EXCEPT} update.
   *
   * <p>Example TLA+: {@code [f EXCEPT ![x] = 0]}.</p>
   *
   * @param function the function expression
   * @param index the updated index
   * @param value the value expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx except(TlaEx function, TlaEx index, TlaEx value) {
    return expression(() -> builder.except(function, index, value));
  }

  /**
   * Creates a sequence with an element appended at the end.
   *
   * <p>Example TLA+: {@code Append(sequence, value)}.</p>
   *
   * @param sequence the sequence expression
   * @param element the element expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx append(TlaEx sequence, TlaEx element) {
    return expression(() -> builder.append(sequence, element));
  }

  /**
   * Creates the concatenation of two sequences.
   *
   * <p>Example TLA+: {@code left \o right}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx concat(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.concat(lhs, rhs));
  }

  /**
   * Creates the first element of a sequence.
   *
   * <p>Example TLA+: {@code Head(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx head(TlaEx sequence) {
    return expression(() -> builder.head(sequence));
  }

  /**
   * Creates the sequence obtained by removing its first element.
   *
   * <p>Example TLA+: {@code Tail(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx tail(TlaEx sequence) {
    return expression(() -> builder.tail(sequence));
  }

  /**
   * Creates the length of a sequence.
   *
   * <p>Example TLA+: {@code Len(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx len(TlaEx sequence) {
    return expression(() -> builder.len(sequence));
  }

  /**
   * Creates the inclusive subsequence between two one-based indices.
   *
   * <p>Example TLA+: {@code SubSeq(sequence, 2, 4)}.</p>
   *
   * @param sequence the sequence expression
   * @param fromIndex the inclusive one-based start index
   * @param toIndex the inclusive one-based end index
   * @return the typed TLA+ IR expression
   */
  public TlaEx subSeq(TlaEx sequence, TlaEx fromIndex, TlaEx toIndex) {
    return expression(() -> builder.subseq(sequence, fromIndex, toIndex));
  }

  /**
   * Creates the primed action expression {@code expression'}.
   *
   * <p>Example TLA+: {@code counter'}.</p>
   *
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx prime(TlaEx expression) {
    return expression(() -> builder.prime(expression));
  }

  /**
   * Creates the stuttering action {@code [action]_expression}.
   *
   * <p>Example TLA+: {@code [Next]_vars}.</p>
   *
   * @param action the action expression
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx stutter(TlaEx action, TlaEx expression) {
    return expression(() -> builder.stutt(action, expression));
  }

  /**
   * Creates the non-stuttering action {@code <action>_expression}.
   *
   * <p>Example TLA+: {@code <Next>_vars}.</p>
   *
   * @param action the action expression
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx noStutter(TlaEx action, TlaEx expression) {
    return expression(() -> builder.nostutt(action, expression));
  }

  /**
   * Creates {@code ENABLED action}.
   *
   * <p>Example TLA+: {@code ENABLED Next}.</p>
   *
   * @param action the action expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx enabled(TlaEx action) {
    return expression(() -> builder.enabled(action));
  }

  /**
   * Creates {@code UNCHANGED expression}.
   *
   * <p>Example TLA+: {@code UNCHANGED vars}.</p>
   *
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx unchanged(TlaEx expression) {
    return expression(() -> builder.unchanged(expression));
  }

  /**
   * Creates the action composition of {@code lhs} followed by {@code rhs}.
   *
   * <p>Example TLA+: {@code First \cdot Second}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx actionThen(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.comp(lhs, rhs));
  }

  /**
   * Creates a TLA+ {@code IF ... THEN ... ELSE ...} expression.
   *
   * <p>Example TLA+: {@code IF condition THEN yes ELSE no}.</p>
   *
   * @param predicate the predicate expression
   * @param whenTrue the expression selected when the predicate is true
   * @param whenFalse the expression selected when the predicate is false
   * @return the typed TLA+ IR expression
   */
  public TlaEx ite(TlaEx predicate, TlaEx whenTrue, TlaEx whenFalse) {
    return expression(() -> builder.ite(predicate, whenTrue, whenFalse));
  }

  /**
   * Creates a TLA+ {@code CASE} expression with no {@code OTHER} branch.
   *
   * <p>Example TLA+: {@code CASE P -> x [] Q -> y}.</p>
   *
   * @param cases one or more condition/result pairs
   * @return the typed TLA+ IR expression
   */
  @SafeVarargs
  public final TlaEx caseSplit(ExpressionPair<TlaEx>... cases) {
    return expression(() -> builder.caseSplit(pairs(cases)));
  }

  /**
   * Creates a TLA+ {@code CASE} expression with an {@code OTHER} result.
   *
   * <p>Example TLA+: {@code CASE P -> x [] OTHER -> y}.</p>
   *
   * @param other the result used when no condition holds
   * @param cases one or more condition/result pairs
   * @return the typed TLA+ IR expression
   */
  @SafeVarargs
  public final TlaEx caseOther(TlaEx other, ExpressionPair<TlaEx>... cases) {
    return expression(() -> builder.caseOther(other, pairs(cases)));
  }

  /**
   * Creates the temporal formula {@code []predicate} (always).
   *
   * <p>Example TLA+: {@code []P}.</p>
   *
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx always(TlaEx predicate) {
    return expression(() -> builder.box(predicate));
  }

  /**
   * Creates the temporal formula {@code <>predicate} (eventually).
   *
   * <p>Example TLA+: {@code <>P}.</p>
   *
   * @param predicate the predicate expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx eventually(TlaEx predicate) {
    return expression(() -> builder.diamond(predicate));
  }

  /**
   * Creates the temporal leads-to formula {@code lhs ~> rhs}.
   *
   * <p>Example TLA+: {@code P ~> Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx leadsTo(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.leadsTo(lhs, rhs));
  }

  /**
   * Creates the temporal guarantees formula {@code lhs -+-> rhs}.
   *
   * <p>Example TLA+: {@code P -+-> Q}.</p>
   *
   * @param lhs the left-hand operand
   * @param rhs the right-hand operand
   * @return the typed TLA+ IR expression
   */
  public TlaEx guarantees(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.guarantees(lhs, rhs));
  }

  /**
   * Creates the weak-fairness condition for an action over the supplied variables.
   *
   * <p>Example TLA+: {@code WF_vars(Next)}.</p>
   *
   * @param variables the state variables
   * @param action the action expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx weakFair(TlaEx variables, TlaEx action) {
    return expression(() -> builder.WF(variables, action));
  }

  /**
   * Creates the strong-fairness condition for an action over the supplied variables.
   *
   * <p>Example TLA+: {@code SF_vars(Next)}.</p>
   *
   * @param variables the state variables
   * @param action the action expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx strongFair(TlaEx variables, TlaEx action) {
    return expression(() -> builder.SF(variables, action));
  }

  /**
   * Creates temporal existential quantification over a variable.
   *
   * <p>Example TLA+: {@code \EE x: P(x)}.</p>
   *
   * @param variable the bound variable expression
   * @param formula the temporal formula
   * @return the typed TLA+ IR expression
   */
  public TlaEx temporalExists(TlaEx variable, TlaEx formula) {
    return expression(() -> builder.EE(variable, formula));
  }

  /**
   * Creates temporal universal quantification over a variable.
   *
   * <p>Example TLA+: {@code \AA x: P(x)}.</p>
   *
   * @param variable the bound variable expression
   * @param formula the temporal formula
   * @return the typed TLA+ IR expression
   */
  public TlaEx temporalForAll(TlaEx variable, TlaEx formula) {
    return expression(() -> builder.AA(variable, formula));
  }

  /**
   * Creates the Apalache assignment {@code lhs := rhs}.
   * <p>In strict mode, {@code lhs} must be a primed variable name.</p>
   *
   * <p>Example TLA+: {@code counter' := counter + 1}.</p>
   *
   * @param lhs the primed variable to assign
   * @param rhs the value assigned to the variable
   * @return the typed TLA+ IR expression
   */
  public TlaEx assign(TlaEx lhs, TlaEx rhs) {
    return expression(() -> builder.assign(lhs, rhs));
  }

  /**
   * Creates an Apalache value generator with an explicit result type.
   * <p>The bound must become a constant expression after preprocessing.</p>
   *
   * <p>Example TLA+: {@code Gen(3)}.</p>
   *
   * @param bound an expression that becomes constant during preprocessing
   * @param returnType the result type
   * @return the typed TLA+ IR expression
   */
  public TlaEx gen(TlaEx bound, TlaType1 returnType) {
    return expression(() -> builder.gen(bound, returnType));
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
   * @return the typed TLA+ IR expression
   */
  public TlaEx repeat(TlaEx operator, BigInteger count, TlaEx initial) {
    return expression(
        () -> builder.repeat(operator, JavaToScalaAdapter$.MODULE$.bigInt(count), initial));
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
   * @return the typed TLA+ IR expression
   */
  public TlaEx repeat(TlaEx operator, long count, TlaEx initial) {
    return repeat(operator, BigInteger.valueOf(count), initial);
  }

  /**
   * Creates Apalache's Skolemization marker for an existential formula.
   * <p>In strict mode, the argument must be an existential quantification.</p>
   *
   * <p>Example TLA+: {@code Skolem(\E x \in S: P(x))}.</p>
   *
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx skolem(TlaEx expression) {
    return expression(() -> builder.skolem(expression));
  }

  /**
   * Creates an Apalache expression that chooses an unspecified member of a set.
   *
   * <p>Example TLA+: {@code Guess(S)}.</p>
   *
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx guess(TlaEx set) {
    return expression(() -> builder.guess(set));
  }

  /**
   * Marks a power set or function set for explicit expansion by Apalache.
   * <p>Strict mode rejects other expression shapes.</p>
   *
   * <p>Example TLA+: {@code Expand(SUBSET S)}.</p>
   *
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx expand(TlaEx expression) {
    return expression(() -> builder.expand(expression));
  }

  /**
   * Marks a constant lower bound on a set's cardinality for Apalache.
   * <p>In strict mode, the argument must have the form {@code Cardinality(set) >= integer}.</p>
   *
   * <p>Example TLA+: {@code ConstCardinality(Cardinality(S) >= 3)}.</p>
   *
   * @param expression the expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx constCard(TlaEx expression) {
    return expression(() -> builder.constCard(expression));
  }

  /**
   * Creates a sequence of a fixed length by applying a unary operator to each index.
   * <p>In strict mode, the length must be nonnegative and the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code MkSeq(3, Elem)}.</p>
   *
   * @param count the sequence length
   * @param operator a unary operator mapping each index to an element
   * @return the typed TLA+ IR expression
   */
  public TlaEx mkSeq(BigInteger count, TlaEx operator) {
    return expression(
        () -> builder.mkSeq(JavaToScalaAdapter$.MODULE$.bigInt(count), operator));
  }

  /**
   * Creates a sequence of a fixed length by applying a unary operator to each index.
   * <p>In strict mode, the length must be nonnegative and the operator must be passed by name.</p>
   *
   * <p>Example TLA+: {@code MkSeq(3, Elem)}.</p>
   *
   * @param count the sequence length
   * @param operator a unary operator mapping each index to an element
   * @return the typed TLA+ IR expression
   */
  public TlaEx mkSeq(long count, TlaEx operator) {
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
   * @return the typed TLA+ IR expression
   */
  public TlaEx mkSeqConst(TlaEx count, TlaEx operator) {
    return expression(() -> builder.mkSeqConst(count, operator));
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
   * @return the typed TLA+ IR expression
   */
  public TlaEx foldSet(TlaEx operator, TlaEx initial, TlaEx set) {
    return expression(() -> builder.foldSet(operator, initial, set));
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
   * @return the typed TLA+ IR expression
   */
  public TlaEx foldSeq(TlaEx operator, TlaEx initial, TlaEx sequence) {
    return expression(() -> builder.foldSeq(operator, initial, sequence));
  }

  /**
   * Treats a set of pairs as a function.
   *
   * <p>Example TLA+: {@code SetAsFun({<<1, "one">>, <<2, "two">>})}.</p>
   *
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx setAsFun(TlaEx set) {
    return expression(() -> builder.setAsFun(set));
  }

  /**
   * Creates a typed placeholder that reports an unsupported expression to the model checker.
   *
   * <p>Example TLA+: {@code __NotSupportedByModelChecker("unsupported")}.</p>
   *
   * @param message the diagnostic reported by the model checker
   * @param type the placeholder expression's result type
   * @return the typed TLA+ IR expression
   */
  public TlaEx notSupportedByModelChecker(String message, TlaType1 type) {
    return expression(() -> builder.notSupportedByModelChecker(message, type));
  }

  /**
   * Creates an internal SMT constraint requiring all arguments to be pairwise distinct.
   *
   * <p>Example TLA+: {@code Distinct(x, y, z)}.</p>
   *
   * @param arguments the argument expressions
   * @return the typed TLA+ IR expression
   */
  public TlaEx distinct(TlaEx... arguments) {
    return expression(() -> builder.distinct(expressions(arguments)));
  }

  /**
   * Creates Apalache's internal capacity value for a sequence.
   *
   * <p>Example TLA+: {@code __ApalacheSeqCapacity(sequence)}.</p>
   *
   * @param sequence the sequence expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx apalacheSeqCapacity(TlaEx sequence) {
    return expression(() -> builder.apalacheSeqCapacity(sequence));
  }

  /**
   * Creates a tagged value of an explicitly supplied variant type.
   *
   * <p>Example TLA+: {@code Variant("Some", 1)}.</p>
   *
   * @param tag the variant tag
   * @param value the value expression
   * @param targetType a variant type containing the supplied tag
   * @return the typed TLA+ IR expression
   */
  public TlaEx variant(String tag, TlaEx value, VariantT1 targetType) {
    return expression(() -> builder.variant(tag, value, targetType));
  }

  /**
   * Extracts the values with a specified tag from a set of variants.
   *
   * <p>Example TLA+: {@code VariantFilter("Some", variants)}.</p>
   *
   * @param tag the tag whose values are selected
   * @param set the set expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx variantFilter(String tag, TlaEx set) {
    return expression(() -> builder.variantFilter(tag, set));
  }

  /**
   * Creates the string tag of a variant value.
   *
   * <p>Example TLA+: {@code VariantTag(variant)}.</p>
   *
   * @param variant the variant expression
   * @return the typed TLA+ IR expression
   */
  public TlaEx variantTag(TlaEx variant) {
    return expression(() -> builder.variantTag(variant));
  }

  /**
   * Extracts the value for a tag, or returns a fallback when the variant has another tag.
   *
   * <p>Example TLA+: {@code VariantGetOrElse("Some", variant, 0)}.</p>
   *
   * @param tag the tag whose value is requested
   * @param variant the variant expression
   * @param defaultValue the fallback value
   * @return the typed TLA+ IR expression
   */
  public TlaEx variantGetOrElse(String tag, TlaEx variant, TlaEx defaultValue) {
    return expression(() -> builder.variantGetOrElse(tag, variant, defaultValue));
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
   * @return the typed TLA+ IR expression
   */
  public TlaEx variantGetUnsafe(String tag, TlaEx variant) {
    return expression(() -> builder.variantGetUnsafe(tag, variant));
  }

  /**
   * Converts Java expression arguments to the collection expected by the underlying builder.
   *
   * @param expressions the expressions to convert
   * @return the underlying expression collection
   */
  private Seq expressions(TlaEx[] expressions) {
    return JavaToScalaAdapter$.MODULE$.uncheckedExpressions(expressions);
  }

  /**
   * Converts expression-pair arguments to the collection expected by the underlying builder.
   *
   * @param pairs the expression pairs to convert
   * @return the underlying expression pairs
   */
  private Seq pairs(ExpressionPair<TlaEx>[] pairs) {
    return JavaToScalaAdapter$.MODULE$.uncheckedPairs(pairs);
  }

  /**
   * Converts named-expression arguments to the collection expected by the underlying builder.
   *
   * @param fields the field definitions
   * @return the underlying named expressions
   */
  private Seq named(NamedExpression<TlaEx>[] fields) {
    return JavaToScalaAdapter$.MODULE$.uncheckedNamed(fields);
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
      throw JavaToScalaAdapter$.MODULE$.translateException(exception);
    }
  }

  /**
   * Runs an expression-building action and maps failures to public facade exceptions.
   *
   * @param action the underlying builder action
   * @return the typed TLA+ IR expression
   */
  private TlaEx expression(Callable<TlaEx> action) {
    return call(action);
  }

  /**
   * Runs a declaration-building action and maps failures to public facade exceptions.
   *
   * @param action the underlying builder action
   * @return the typed TLA+ IR operator declaration
   */
  private TlaOperDecl declaration(Callable<TlaOperDecl> action) {
    return call(action);
  }
}
