package at.forsyte.apalache.tla.lir

/**
 * The level of a TLA+ expression, as explained in: Lamport. Specifying Systems, p. 322.
 */
sealed trait TlaLevel extends Ordered[TlaLevel] {

  /**
   * The level number as assigned in the book.
   */
  val level: Int

  /**
   * A textual representation of the level.
   */
  val name: String

  /**
   * Compare this level to another level.
   *
   * @param that the level to compare
   * @return 0, if the levels are equal; a negative number if `this` is smaller than `that`, and a positive number
   *         if `this` is larger than `that`.
   */
  override def compare(that: TlaLevel): Int = {
    level - that.level
  }

  /**
   * Join the levels by computing the maximum of the levels of `this` and `that`.
   *
   * @param that the level to join with
   * @return the minimal level j that satisfies: `j <= this` and `j <= that`.
   */
  def join(that: TlaLevel): TlaLevel = {
    TlaLevel.fromInt(Math.max(level, that.level))
  }

  /**
   * Join the level with a sequence of level.
   *
   * @param otherLevels a sequence of levels
   * @return the join of `this` and otherLevels
   */
  def join(otherLevels: Seq[TlaLevel]): TlaLevel = {
    otherLevels.foldLeft(this) { case (l, r) => l.join(r) }
  }
}

object TlaLevel {
  private val INT_TO_LEVEL = Seq(TlaLevelConst, TlaLevelState, TlaLevelAction, TlaLevelTemporal)

  def fromInt(levelNo: Int): TlaLevel = {
    INT_TO_LEVEL.find(_.level == levelNo) match {
      case Some(level) => level

      case None =>
        throw new IllegalArgumentException(s"Unexpected level: $levelNo")
    }
  }
}

/**
 * Constant level: constants and constant-level expressions.
 */
case object TlaLevelConst extends TlaLevel {
  override val level: Int = 0
  override val name: String = "Constant"
}

/**
 * State level: the constant-level, state variables, and expressions over them that are not actions or temporal formulas.
 */
case object TlaLevelState extends TlaLevel {
  override val level: Int = 1
  override val name: String = "State"
}

/**
 * Action level: the state level, state variables, primed state variables, and action operators.
 */
case object TlaLevelAction extends TlaLevel {
  override val level: Int = 2
  override val name: String = "Action"
}

/**
 * Temporal level: the action level and temporal formulas.
 */
case object TlaLevelTemporal extends TlaLevel {
  override val level: Int = 3
  override val name: String = "Temporal"
}
