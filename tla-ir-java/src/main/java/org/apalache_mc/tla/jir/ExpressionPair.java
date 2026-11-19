package org.apalache_mc.tla.jir;

/**
 * Two expressions that form a binding or a TLA+ {@code CASE} branch.
 *
 * <p>For {@code map} and {@code funDef}, {@code first} is the bound name and {@code second} is its domain set. For
 * {@code caseSplit} and {@code caseOther}, {@code first} is the condition and {@code second} is the branch result.</p>
 *
 * @param first the bound name or branch condition
 * @param second the domain set or branch result
 * @param <E> {@link TlaBuilderExpr} or {@code TlaEx}, depending on the builder in use
 */
public record ExpressionPair<E>(E first, E second) {}
