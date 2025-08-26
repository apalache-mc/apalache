package at.forsyte.apalache.io.annotations.parser

/**
 * <p>This class preprocesses comments as they are produced by SANY and does the following:</p>
 *
 * <ul> <li>Unconditionally remove the comment tokens: (*, *), and \*.</li> <li>Extract candidates for annotations.</li>
 * <li>Exclude candidates for annotations in double comments, e.g., (* (* ... *) *).</li> <li>Preserve the text outside
 * the annotations and double comments. </ul>
 *
 * <p>The main design principle of the preprocessor is that it should not fail on any input. The preprocessor should
 * respect the structure of the comments, but it may return ill-formed annotations, if they are ill-formed in the
 * original text. This preprocessor prunes the comment tokens, even in arguably valid cases (e.g., inside a string).
 * Although it is usually not a good idea to write an ad-hoc lexer, it is not obvious to me, how to use a lexer
 * generator here. However, if someone knows how to write this preprocessor with a lexer generator, let me know.
 * Perhaps, the first step would be to write a precise grammar for this lexer, instead of write the spaghetti of
 * if-then-else expressions, as we have in this preprocessor.</p>
 *
 * <p>See the annotations HOWTO: https://apalache-mc.org/docs/HOWTOs/howto-write-type-annotations.html</p>
 *
 * @author
 *   Igor Konnov
 */
class CommentPreprocessor {
  private val tokenRegex = """(\n|\\\*|\(\*|\*\)|@[a-zA-Z_][a-zA-Z0-9_]*|\)|;|")""".r

  // internal state of the preprocessor
  private case class State(
      inOneLineComment: Boolean = false,
      multiCommentLevel: Int = 0,
      inParensAnnotation: Boolean = false,
      inColonAnnotation: Boolean = false,
      inString: Boolean = false) {
    def enterParensAnnotation(): State = {
      // when entering an annotation, we can be neither inside a string, nor in another annotation
      this.copy(inParensAnnotation = true, inColonAnnotation = false, inString = false)
    }

    def enterColonAnnotation(): State = {
      // when entering an annotation, we can be neither inside a string, nor in another annotation
      this.copy(inParensAnnotation = false, inColonAnnotation = true, inString = false)
    }

    def leaveAnnotation(): State = {
      // when entering an annotation, we can be neither inside a string, nor in another annotation
      this.copy(inParensAnnotation = false, inColonAnnotation = false, inString = false)
    }

    def enterString(): State = {
      this.copy(inString = true)
    }

    def leaveString(): State = {
      this.copy(inString = false)
    }

    def enterOneLineComment(): State = {
      this.copy(inOneLineComment = true)
    }

    def leaveOneLineComment(): State = {
      this.copy(inOneLineComment = false)
    }

    def increaseCommentLevel(): State = {
      if (!inOneLineComment) {
        this.copy(multiCommentLevel = multiCommentLevel + 1)
      } else {
        // a multi-level comment is ignored inside a single-line comment
        // \* ... (* ....
        this
      }
    }

    def decreaseCommentLevel(): State = {
      // Importantly, *) closes a one-line comment, if it was prepended with (*.
      // This is not exactly compatible with SANY, but, e.g., it is compatible with TLA+ syntax highlighting in vim.
      (inOneLineComment, multiCommentLevel > 0) match {
        case (false, false) => this
        case (_, true)      => this.copy(inOneLineComment = false, multiCommentLevel - 1)
        case (true, false)  => this.copy(inOneLineComment = false, multiCommentLevel = 0)
      }
    }

    def isExcludingText: Boolean = {
      (inOneLineComment && multiCommentLevel > 0) || multiCommentLevel > 1
    }

    def inAnnotation: Boolean = {
      inColonAnnotation || inParensAnnotation
    }
  }

  /**
   * Given a multiline string, remove noisy tokens and find potential annotations.
   *
   * @param text
   *   input string
   * @return
   *   the string without the noisy tokens and potential annotations and potential annotations
   */
  def apply(text: String): (String, List[String]) = {
    val textBuilder = new StringBuilder()
    var annotationBuilder = new StringBuilder()
    var annotations: List[String] = List()
    var lastIndexOfUnmatchedText = 0
    var state = State()
    val matchIterator = tokenRegex.findAllIn(text)
    while (matchIterator.hasNext) {
      val group = matchIterator.next()
      val isGoodStartForAnnotation = isValidCharBeforeAnnotation(text, matchIterator.start)
      if (matchIterator.start > lastIndexOfUnmatchedText && !state.isExcludingText) {
        // add the text between the last match and this match
        val fragment = text.substring(lastIndexOfUnmatchedText, matchIterator.start)
        if (state.inAnnotation) {
          annotationBuilder.append(fragment)
        } else {
          textBuilder.append(fragment)
        }
      }
      // advance the index of the unmatched text
      lastIndexOfUnmatchedText = matchIterator.end
      // do not eat the special tokens
      if (!state.inAnnotation && (group == "\n" || group == ")" || group == ";" || group == "\"")) {
        textBuilder.append(group)
      }
      // look one character ahead to figure out the annotation type
      val lookaheadChar = if (lastIndexOfUnmatchedText < text.length) Some(text(lastIndexOfUnmatchedText)) else None
      // figure out whether we have met an annotation or not
      if (!state.inAnnotation && !state.inString && group.startsWith("@")) {
        if (!isGoodStartForAnnotation) {
          // this is not an annotation, push it back to the free text
          textBuilder.append(group)
        } else {
          if (lookaheadChar.contains(':') || lookaheadChar.contains('(')) {
            // Advance the last unmatched index beyond "@annotation:" or "@annotation(".
            lastIndexOfUnmatchedText += 1
          } else if (isEndOfParameterlessAnnotation(lookaheadChar)) {
            // Add this annotation immediately.
            // Do not advance the index in case of "@annotation " or similar.
            annotations = annotations :+ group.trim
          } else {
            // this is not an annotation, push it back to the free text
            textBuilder.append(group)
          }
        }
      }

      val nextState = getNextState(state, group, lookaheadChar, isGoodStartForAnnotation)

      (state.inAnnotation, nextState.inAnnotation) match {
        case (false, false) => ()

        case (false, true) =>
          // open an annotation
          annotationBuilder = new StringBuilder()
          annotationBuilder.append(group.trim)
          // don't forget '(' or ':' that are stored in look-ahead
          annotationBuilder.append(lookaheadChar.get)

        case (true, true) =>
          // This must NOT ignore new lines, or else we lose the ability to identify
          // single-line comments in type annotations.
          // See https://github.com/apalache-mc/apalache/issues/2162
          if (group != "\\*" && group != "(*" && group != "*)") {
            annotationBuilder.append(group)
          } // else: prune the comment characters and line-feed

        case (true, false) =>
          // close the annotation
          annotationBuilder.append(group)
          annotations = annotations :+ annotationBuilder.toString()
          annotationBuilder = new StringBuilder()
      }

      state = nextState
    }

    if (lastIndexOfUnmatchedText < text.length) {
      // mind the text after the last matched group
      textBuilder.append(text.substring(lastIndexOfUnmatchedText))
    }

    if (annotationBuilder.nonEmpty) {
      // an open annotation is not closed, add to the annotation, so the annotation parser fails later
      annotations = annotations :+ annotationBuilder.toString()
    }

    (textBuilder.toString(), annotations)
  }

  private def isValidCharBeforeAnnotation(text: String, index: Int): Boolean = {
    if (index == 0) {
      true
    } else {
      val char = text(index - 1)
      // @foo is written either after a whitespace (to exclude emails), or after the comment token, e.g., (* or \*
      char.isWhitespace || char == '*'
    }
  }

  private def getNextState(
      state: State,
      group: String,
      lookaheadChar: Option[Char],
      isGoodStartForAnnotation: Boolean): State = {
    group match {
      case "\\*" =>
        state.enterOneLineComment()

      case "\n" =>
        if (state.inOneLineComment) {
          state.leaveOneLineComment()
        } else {
          state
        }

      case "\"" =>
        if (state.inColonAnnotation) {
          // ignore in @annotation: ...;
          state
        } else {
          if (state.inString) {
            state.leaveString()
          } else {
            state.enterString()
          }
        }

      case "(*" =>
        state.increaseCommentLevel()

      case "*)" =>
        state.decreaseCommentLevel()

      case ")" =>
        if (state.inString || state.inColonAnnotation) {
          // just ')' inside a string "..." or inside @annotation: ...;
          state
        } else {
          state.leaveAnnotation()
        }

      case ";" =>
        if (state.inString || !state.inAnnotation) {
          // just copy ';' inside a string or outside an annotation
          state
        } else {
          state.leaveAnnotation()
        }

      case _ =>
        if (!group.startsWith("@") || !isGoodStartForAnnotation) {
          state
        } else {
          if (lookaheadChar.contains('(') && !state.inAnnotation) {
            state.enterParensAnnotation()
          } else if (lookaheadChar.contains(':') && !state.inAnnotation) {
            state.enterColonAnnotation()
          } else if (!state.inAnnotation && isEndOfParameterlessAnnotation(lookaheadChar)) {
            // an annotation like "@awesome " is immediately consumed
            state
          } else {
            if (state.inString) {
              // Somebody wrote an annotation inside a string, which resides inside an annotation. Life is tough.
              state
            } else {
              // Most likely, the current annotation has not been closed.
              // The only option we have is to leave the previous annotation and propagate the new one into the main text.
              state.leaveAnnotation()
            }
          }
        }
    }
  }

  private def isEndOfParameterlessAnnotation(lookaheadChar: Option[Char]): Boolean = {
    lookaheadChar.isEmpty || lookaheadChar.exists(c => " \n\t\r*".contains(c))
  }
}

object CommentPreprocessor {
  def apply(): CommentPreprocessor = {
    new CommentPreprocessor()
  }
}
