package at.forsyte.apalache.tla.bmcmt.trex

/**
 * A state of the executor context:
 *
 * <ul>
 *   <li>In <b>Preparing</b>, new transitions and assertions may be added to the current state.</li>
 *   <li>In <b>Picked</b>, a transition has been fixed. Only assertions may be added.</li>
 * </ul>
 *
 * @author Igor Konnov
 */
abstract class ExecutorControlState {}

/**
 * New transitions and assertions may be added to the current state.
 */
case class Preparing() extends ExecutorControlState

/**
 * A transition has been fixed. Only assertions may be added.
 */
case class Picked() extends ExecutorControlState
