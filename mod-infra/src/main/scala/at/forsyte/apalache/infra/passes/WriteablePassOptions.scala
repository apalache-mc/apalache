package at.forsyte.apalache.infra.passes

import scala.reflect.ClassTag
import at.forsyte.apalache.infra.PassOptionException
import com.google.inject.Singleton

import scala.collection.mutable

/**
 * A writeable (mutable) extension of [[PassOptions]]
 *
 * This class is used only internally. When you implement your own pass, use the trait [[PassOptions]].
 *
 * @author
 *   Igor Konnov
 */
@Singleton
class WriteablePassOptions extends PassOptions {
  private val store: mutable.Map[String, Any] = mutable.HashMap[String, Any]()

  /**
   * Set a pass option
   * @param name
   *   an option name, where the pass name is separated from the option name with a dot (.)
   * @param value
   *   an option value
   */
  def set(name: String, value: Any): Unit = {
    if (!name.exists(_ == '.')) {
      throw new PassOptionException("Expected an option of format <pass>.<option, found: " + name)
    }
    store += (name -> value)
  }

  /**
   * Get a pass option
   * @param passName
   *   a pass name, or any other convenient name
   * @param optionName
   *   an option name
   * @return
   *   the option value, normally, an Integer or String
   */
  def get[T: ClassTag](passName: String, optionName: String): Option[T] = {
    // The ClassTag prevents the type of `T` from being erased at runtime
    // See https://stackoverflow.com/a/18136667/1187277
    store.get(passName + "." + optionName) match {
      // Since we have added the ClassTag, we are able to match on its value here
      case Some(value: T) =>
        Some(value)

      case Some(value) =>
        throw new IllegalArgumentException(s"Option $optionName has unexpected type: " + value.getClass)

      case None => None
    }
  }

  /**
   * Get a pass option, or fallback to the default value
   *
   * @param passName
   *   a pass name, or any other convenient name
   * @param optionName
   *   an option name
   * @param default
   *   a default value
   * @return
   *   the option value, normally, an Integer or String
   */
  def getOrElse[T: ClassTag](passName: String, optionName: String, default: T): T = {
    val value = get[T](passName, optionName)
    if (value.isDefined) {
      value.get.asInstanceOf[T]
    } else {
      default
    }
  }

  /**
   * Get a pass option. If there is no such option, throw an OptionException.
   *
   * @param passName
   *   a pass name, or any other convenient name
   * @param optionName
   *   an option name
   * @return
   *   the option value, normally, an Integer or String
   */
  def getOrError[T: ClassTag](passName: String, optionName: String): T = {
    val value = get[T](passName, optionName)
    if (value.isDefined) {
      value.get.asInstanceOf[T]
    } else {
      throw new PassOptionException("The mandatory option %s.%s not found"
            .format(passName, optionName))
    }
  }

}
