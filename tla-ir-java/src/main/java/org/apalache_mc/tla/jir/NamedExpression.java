package org.apalache_mc.tla.jir;

/**
 * A named field and the expression associated with it.
 *
 * <p>Use instances with {@code record} and {@code recordSet}. For a record, the expression is the field value; for a
 * record set, it is the set of permitted field values.</p>
 *
 * @param name the field name
 * @param expression the field value or set of permitted values
 * @param <E> {@link TlaBuilderExpr} or {@code TlaEx}, depending on the builder in use
 */
public record NamedExpression<E>(String name, E expression) {}
