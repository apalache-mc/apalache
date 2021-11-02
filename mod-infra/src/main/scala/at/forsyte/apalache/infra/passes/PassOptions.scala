package at.forsyte.apalache.infra.passes
import scala.reflect.ClassTag

/**
 * The central store for various options given to the passes.
 * An option is a key-value pair. By convention, a key is a string
 * of the shape pass.option, where pass is the pass name and option is the option name.
 * A pass name does not have to match exactly the name of the pass that is accessing
 * the option, but of a class of passes. For instance, the option parser.filename can be
 * used by all parsing passes, not just the pass called 'parser'.
 *
 * @author Igor Konnov
 */
trait PassOptions {

  // The `ClassTag` is needed to prevent the type of `T` being erased,
  // because we expect implementations to make use of the type at runtime.
  /**
   * Get a pass option.
   *
   * @param passName   a pass name, or any other convenient name
   * @param optionName an option name
   * @return the option value, normally, an Integer or String
   */
  def get[T: ClassTag](passName: String, optionName: String): Option[T]

  /**
   * Get a pass option, or fallback to the default value
   *
   * @param passName   a pass name, or any other convenient name
   * @param optionName an option name
   * @param default    a default value
   * @return the option value, normally, an Integer or String
   */
  def getOrElse[T](passName: String, optionName: String, default: T): T

  /**
   * Get a pass option. If there is no such option, throw an OptionException.
   *
   * @param passName   a pass name, or any other convenient name
   * @param optionName an option name
   * @return the option value, normally, an Integer or String
   */
  def getOrError[T](passName: String, optionName: String): T
}
