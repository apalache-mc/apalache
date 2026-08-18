package org.apalache_mc.tla.jir;

/**
 * One replacement in a TLA+ {@code EXCEPT} expression.
 *
 * <p>Pass one or more updates to a builder's {@code exceptMany} method. The {@code index} selects the function entry
 * to replace, and {@code value} is the expression stored at that entry.</p>
 *
 * @param index the function argument whose entry is replaced
 * @param value the expression stored at the selected entry
 * @param <E> {@link TlaBuilderExpr} or {@code TlaEx}, depending on the builder in use
 */
public record ExceptUpdate<E>(E index, E value) {}
