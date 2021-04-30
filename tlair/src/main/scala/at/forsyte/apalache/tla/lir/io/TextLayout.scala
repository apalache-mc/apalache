package at.forsyte.apalache.tla.lir.io

/**
 * Settings for text output.
 *
 * @param textWidth the length of a single line.
 * @param indent    the number of characters in a single level of indentation.
 */
case class TextLayout(val textWidth: Int = 80, val indent: Int = 2) {}
