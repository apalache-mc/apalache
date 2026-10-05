package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.TlaType1;

/**
 * The type of one field in a sparse tuple.
 *
 * <p>Use instances as arguments to {@code TlaTypes.sparseTuple}. Indices identify the tuple positions that are present
 * and need not be consecutive.</p>
 *
 * @param index the one-based tuple position
 * @param type the type at that position
 */
public record IndexedType(int index, TlaType1 type) {}
