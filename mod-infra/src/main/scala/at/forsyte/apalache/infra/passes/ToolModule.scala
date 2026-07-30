package at.forsyte.apalache.infra.passes

import com.google.inject.AbstractModule

/**
 * An extension of Google Guice AbstractModule used to configure a pass sequence.
 *
 * Concrete modules accept validated, mode-specific options and bind only the option components consumed by
 * their passes.
 *
 * @author
 *   Gabriela Moreira
 * @author
 *   Shon Feder
 */
abstract class ToolModule extends AbstractModule {

  /**
   * The sequence of passes that need to be run for the module
   *
   * @return
   *   the sequence of passes
   */
  def passes: Seq[Class[_ <: Pass]]
}
