package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.passes.Pass.PassResult
import at.forsyte.apalache.tla.lir.ModuleProperty
import at.forsyte.apalache.tla.lir.TlaModule
import upickle.default.Writer
import upickle.default.writeJs

/**
 * <p>An analysis or transformation pass. Instead of explicitly setting a pass' input and output, we interconnect passes
 * with Google Guice and delegate the actual calls to the pass. Thus, normally, passes follow a pipeline, but they also
 * can follow an arbitrary graph.</p>
 *
 * <p>Note that the passes must be stateless, as no guarantee is provided on that the same pass is called several times.
 * When a pass finishes its job, it should set up the properties of the next pass.</p>
 *
 * <p>If you are looking for a way to store intermediate results, use a KeyValueStore.</p>
 *
 * @author
 *   Igor Konnov
 * @author
 *   Shon Feder
 */
trait Pass {

  /**
   * The pass name.
   *
   * @return
   *   the name associated with the pass
   */
  def name: String

  var passNumber: Int = 0

  /**
   * Updates the pass number internally
   *
   * @return
   *   This pass, with an updated pass number
   */
  def withNumber(i: Int): Pass = {
    passNumber = i
    this
  }

  /**
   * Run the pass.
   * @param module
   *   The module to be transformed by the pass
   *
   * @return
   *   the transformed module, if the pass was successful
   */
  def execute(module: TlaModule): PassResult

  /**
   * List the dependencies of the pass. These are properties the module has to have in order to be processed by the
   * pass. Transitive dependencies are ignored, so if A depends on B and B depends on C The possible dependency from A
   * to C will not be declared
   *
   * @return
   *   the set of dependencies
   */
  def dependencies: Set[ModuleProperty.Value]

  /**
   * List transformations the pass applies. These are properties the module will additionally have at the end of the
   * execution
   *
   * @return
   *   the set of transformations
   */
  def transformations: Set[ModuleProperty.Value]

  /**
   * Construct a failing pass result
   *
   * To be called to construct a failing `PassResult` in the event that a pass fails.
   *
   * @param errorData
   *   Data providing insights into the reasons for the failure.
   * @param exitCode
   *   The exit code to be used when terminating the program.
   * @param f
   *   An implicit upickle writer than can convert the `errorData` into json. You can import `upickle.default._` to get
   *   implicits for common datatypes. For an example of defining a custom writer, see
   *   `at.forsyte.apalache.tla.bmcmt.Counterexample`.
   */
  def passFailure[E](errorData: E, exitCode: TExitCode)(implicit f: Writer[E]): PassResult =
    Left(Pass.PassFailure(name, writeJs(errorData), exitCode))
}

object Pass {

  import upickle.implicits.key

  /**
   * Represents a failing pass
   *
   * @param passName
   *   The name of the pass which has failed.
   * @param errorData
   *   Data providing insights into the reasons for the failure.
   * @param exitCode
   *   The exit code to be used when terminating the program.
   */
  case class PassFailure(
      @key("pass_name") passName: String,
      @key("error_data") errorData: ujson.Value,
      @key("exit_code") exitCode: TExitCode) {}

  /** Implicit conversions for [[PassFailure]] */
  object PassFailure {
    import upickle.default.{macroRW, writeJs, ReadWriter}

    implicit val upickleReadWriter: ReadWriter[PassFailure] = macroRW

    implicit val ujsonView: PassFailure => ujson.Value = writeJs
  }

  type PassResult = Either[PassFailure, TlaModule]
}
