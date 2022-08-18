package at.forsyte.apalache.infra.passes

import com.google.inject.AbstractModule
import at.forsyte.apalache.infra.passes.options.OptionGroup
import com.google.inject.TypeLiteral

/**
 * An extension of Google Guice AbstractModule to be used by apalache modules to configure pass order and options.
 *
 * `ToolModule`'s are parameterized on a [[at.forsyte.apalache.infra.passes.options.OptionGroup OptionGroup]], which
 * statically enforces the connection between a particular sequence of passes and the set of options which are required
 * to run those passes. In the degenerate case were no options are needed for a sequnece of passes, classes can extend
 * `ToolModule(OptionGroup.Empty())`.
 *
 * Every subclass of `ToolModule` should end it's `configure` method by calling `super.configure()`, which ensures the
 * needed options are available for passes.
 *
 * Subclasses are generally expected to reduce the upper bound on `O`, giving a more precise specification of the
 * options required to run the passesses.
 *
 * @author
 *   Gabriela Moreira
 * @author
 *   Shon Feder
 */
abstract class ToolModule[O <: OptionGroup](options: O) extends AbstractModule {

  /**
   * The sequence of passes that need to be run for the module
   *
   * @return
   *   the sequence of passes
   */
  def passes: Seq[Class[_ <: Pass]]

  /** The base configuration of the passes */
  override def configure(): Unit = {
    // The specific type of `OptionGroup` is determined by the `options`  to
    // which the `ToolModule` is applied.  `TypeLiteral` lets us bind the
    // supplied options to the type that is eventually derived for the generic
    // `O`.
    //
    // For more on `TypeLiteral`, see
    // https://google.github.io/guice/api-docs/4.1/javadoc/com/google/inject/TypeLiteral.html
    bind(new TypeLiteral[O]() {}).toInstance(options)
  }
}
