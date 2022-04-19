package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.typecmp.subbuilder.{ArithmeticBuilder, BoolBuilder, LeafBuilder}

/**
 * Builder that, on top of guaranteeing type-correctness, also ensures scope consistency (i.e. guarantees that variables
 * always have the same type within any scope they are defined in)
 *
 * @author
 *   Jure Kukovec
 */
class ScopedBuilder(val sigGen: SignatureGenerator) extends BoolBuilder with ArithmeticBuilder with LeafBuilder
