package at.forsyte.apalache.tla.passes.pp

import at.forsyte.apalache.tla.imp.passes.PassWithOutputs

/**
 * A pass that encodes temporal properties as invariants.
 *
 * @author
 *   Philip Offtermatt
 */
trait TemporalPass extends PassWithOutputs
