package at.forsyte.apalache.tla.pp

import java.util.concurrent.atomic.AtomicLong

import com.google.inject.Singleton

/**
  * A generator of unique and concise names. This class is used to produce unique names in bindings.
  * To guarantee uniqueness, this class is annotated with @Singleton, so Google Guice will instantiate it only once.
  *
  * Importantly, this name is deterministic, that is, it produces names in sequence. This class is thread-safe.
  *
  * @author Igor Konnov
  */
@Singleton
class UniqueNameGenerator {
  private var nextId: AtomicLong = new AtomicLong(1)

  /**
    * Produce a new unique name for a variable
    * @return a name starting with "_T" followed by letters and digits
    */
  def newName(): String = {
    val id = nextId.getAndIncrement()
    "t_" + numToStr(id)
  }

  private def numToStr(num: Long): String = {
    if (num == 0)
      ""
    else {
      val index = (num % UniqueNameGenerator.N_LETTERS).toInt
      val letter = UniqueNameGenerator.LETTERS(index)
      numToStr(num / UniqueNameGenerator.N_LETTERS) + letter
    }
  }
}

object UniqueNameGenerator {
  /**
    * The characters used in generated names
    */
  val LETTERS: Array[String] =
    Array(
      "0", "1", "2", "3", "4", "5", "6", "7", "8", "9",
      "a", "b", "c", "d", "e", "f", "g", "h", "i", "j",
      "k", "l", "m", "n", "o", "p", "q", "r", "s", "t",
      "u", "v", "w", "x", "y", "z"
    ) ////

  /**
    * The number of characters in the table.
    */
  val N_LETTERS: Long = LETTERS.length
}
