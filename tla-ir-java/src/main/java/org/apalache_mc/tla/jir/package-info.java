/**
 * Constructs typed Apalache TLA+ intermediate-representation values from Java.
 *
 * <p>{@link org.apalache_mc.tla.jir.TlaCheckedBuilder} is the primary entry point for building expressions and
 * declarations with type and scope validation. {@link org.apalache_mc.tla.jir.TlaTypedScopeUncheckedBuilder} is
 * available to callers that already guarantee lexical scope. {@link org.apalache_mc.tla.jir.TlaTypes} and
 * {@link org.apalache_mc.tla.jir.TlaDeclarations} provide the supporting type and declaration factories.</p>
 */
@NullMarked
package org.apalache_mc.tla.jir;

import org.jspecify.annotations.NullMarked;
