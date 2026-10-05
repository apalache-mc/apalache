package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.TlaType1;

/**
 * A named field and its TLA+ type.
 *
 * <p>Use instances with the record, row, row-record, and variant factories in {@link TlaTypes}.</p>
 *
 * @param name the field or variant-option name
 * @param type the associated value type
 */
public record NamedType(String name, TlaType1 type) {}
