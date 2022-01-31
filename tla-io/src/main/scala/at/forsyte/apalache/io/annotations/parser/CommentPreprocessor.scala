package at.forsyte.apalache.io.annotations.parser

/**
 * <p>This class preprocesses comments as they are produced by SANY and does the following:</p>
 *
 * <ul>
 * <li>Unconditionally remove the comment tokens: (*, *), and \*.</li>
 * <li>Extract candidates for annotations.</li>
 * <li>Exclude candidates for annotations in double comments, e.g., (* (* ... *) *).</li>
 * <li>Preserve the text outside the annotations and double comments.
 * </ul>
 *
 * <p>The main design principle of the preprocessor is that it should not fail on any input.
 * The preprocessor should respect the structure of the comments, but it may return ill-formed
 * annotations, if they are ill-formed in the original text. This preprocessor prunes the comment
 * tokens, even in arguably valid cases (e.g., inside a string). Although it is usually not a good idea
 * to write an ad-hoc lexer, it is not obvious to me, how to use a lexer generator here.
 * </p>
 *
 * <p>See the annotations HOWTO: https://apalache.informal.systems/docs/HOWTOs/howto-write-type-annotations.html</p>
 *
 * @author Igor Konnov
 */
class CommentPreprocessor {
  private val tokenRegex = """(\n|\\\*|\(\*|\*\)|@[a-zA-Z_][a-zA-Z0-9_]*[ \t\r]*[:(]|\)|;|")""".r

  // internal state of the preprocessor
  private case class State(inOneLineComment: Boolean = false, multiCommentLevel: Int = 0,
      inParensAnnotation: Boolean = false, inColonAnnotation: Boolean = false, inString: Boolean = false) {
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
        // a multi-level comment is ignored inside a multi-level comment
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
   * @param text input string
   * @return the string without the noisy tokens and potential annotations and potential annotations
   */
  def apply(text: String): (String, List[String]) = {
    val textBuilder = new StringBuilder()
    var annotationBuilder = new StringBuilder()
    var annotations: List[String] = List()
    var lastIndex = 0
    var state = State()
    val matchIterator = tokenRegex.findAllIn(text)
    while (matchIterator.hasNext) {
      val group = matchIterator.next()
      if (matchIterator.start > lastIndex && !state.isExcludingText) {
        // add the text between the last match and this match
        val fragment = text.substring(lastIndex, matchIterator.start)
        if (state.inAnnotation) {
          annotationBuilder.append(fragment)
        } else {
          textBuilder.append(fragment)
        }
      }
      if ((group == "\n" || group == ")" || group == ";" || group == "\"") && !state.inAnnotation) {
        textBuilder.append(group)
      }
      val nextState = getNextState(state, group)

      (state.inAnnotation, nextState.inAnnotation) match {
        case (false, false) => ()

        case (false, true) =>
          // open an annotation
          annotationBuilder = new StringBuilder()
          annotationBuilder.append(group)

        case (true, true) =>
          if (group != "\\*" && group != "(*" && group != "*)" && group != "\n") {
            annotationBuilder.append(group)
          } // else: prune the comment characters and line-feed

        case (true, false) =>
          // close the annotation
          annotationBuilder.append(group)
          annotations = annotations :+ annotationBuilder.toString()
          annotationBuilder = new StringBuilder()
      }

      state = nextState
      lastIndex = matchIterator.end
    }

    if (lastIndex < text.length) {
      // mind the text after the last matched group
      textBuilder.append(text.substring(lastIndex))
    }

    if (annotationBuilder.nonEmpty) {
      // an open annotation is not closed, add to the annotation, so the annotation parser fails later
      annotations = annotations :+ annotationBuilder.toString()
    }

    (textBuilder.toString(), annotations)
  }

  private def getNextState(state: State, group: String): State = {
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
        if (!group.startsWith("@")) {
          state
        } else {
          if (group.endsWith("(") && !state.inAnnotation) {
            state.enterParensAnnotation()
          } else if (group.endsWith(":") && !state.inAnnotation) {
            state.enterColonAnnotation()
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
}

object CommentPreprocessor {
  def apply(): CommentPreprocessor = {
    new CommentPreprocessor()
  }
}
