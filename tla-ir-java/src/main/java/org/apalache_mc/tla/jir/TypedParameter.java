package org.apalache_mc.tla.jir;

import at.forsyte.apalache.tla.lir.TlaType1;

/**
 * The name and TLA+ type of an operator parameter.
 *
 * <p>Create parameters with a builder's {@code param} method, then pass them to {@code decl} or {@code lambda}. The
 * type may describe either a value parameter or a higher-order operator parameter.</p>
 *
 * @param name the parameter name as it appears in the operator body
 * @param type the value or operator type accepted by the parameter
 */
public record TypedParameter(String name, TlaType1 type) {}
