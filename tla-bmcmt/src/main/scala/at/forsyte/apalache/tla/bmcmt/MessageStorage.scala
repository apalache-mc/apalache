package at.forsyte.apalache.tla.bmcmt

/**
 * This is trait that allows one to associate a text message with an integer id.
 * The main usage is to associate error messages with the Boolean flags that specify assertion violations.
 *
 * @author Igor Konnov
 */
trait MessageStorage {

  /**
   * Add a text message to the storage.
   * @param id an id of the object, e.g., ArenaCell.id
   * @param message a text message
   */
  def addMessage(id: Int, message: String): Unit

  /**
   * Find a message associated with the given id
   * @param id an id of the object, e.g., ArenaCell.id
   * @return a text message, if exists
   * @throws NoSuchElementException if there is no message associated with the given id
   */
  def findMessage(id: Int): String
}
