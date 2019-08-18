package at.forsyte.apalache.tla.lir.io

import java.io.PrintWriter

import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.io.PrettyWriter._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.convenience._

import scala.collection.immutable.HashMap

/**
  * <p>A pretty printer to a file that formats a TLA+ expression to a given text width (normally, 80 characters)
  * and follows the indentation rules for /\ and \/. Our approach to indentation is inspired by the
  * <a href="https://caml.inria.fr/resources/doc/guides/format.en.html">Format module in OCaml</a>.</p>
  *
  * @author Igor Konnov
  */
class PrettyWriter(writer: PrintWriter, textWidth: Int = 80) {
  def write(expr: TlaEx): Unit = {
    toFormatElem((0, 0), expr).write(new WindowWriter(writer, textWidth))
  }

  def toFormatElem(parentPrecedence: (Int, Int), expr: TlaEx): FormatElem = {
    // TODO: some operators are still calling UTFPrinter, fix it
    expr match {
      case NameEx(x) => TextElem(x)

      case ValEx(TlaStr(text)) => TextElem("\"%s\"".format(text))
      case ValEx(TlaInt(value)) => TextElem(value.toString)
      case ValEx(TlaBool(b)) => TextElem(if (b) "TRUE" else "FALSE")
      case ValEx(TlaBoolSet) => TextElem("BOOLEAN")
      case ValEx(TlaIntSet) => TextElem("Int")
      case ValEx(TlaNatSet) => TextElem("Nat")
      case ValEx(TlaRealSet) => TextElem("Real")
      case ValEx(TlaStrSet) => TextElem("STRING")

      case OperEx(op, args@_*) if op == TlaBoolOper.and || op == TlaBoolOper.or =>
        // we are not using indented /\ and \/, as they are hard to get automatically
        val sign = if (op == TlaBoolOper.and) " /\\ " else " \\/ "

        if (args.isEmpty) {
          val const = tla.bool(op == TlaBoolOper.and)
          toFormatElem(parentPrecedence, const)
        } else {
          val hbox =
            HovBox(
              toFormatElem(op.precedence, args.head), // the first element should not be indented
              IndentBox(  // the reset may be indented
                HovBox(args.tail map (toFormatElem(op.precedence, _)): _*).
                  setSep(sign).
                  setIsHangingSep(false)
              )).
              setSep(sign).setIsHangingSep(false) ///

          wrapWithParen(parentPrecedence, op.precedence, hbox)
        }

      case OperEx(op, x, set, pred)
        if op == TlaBoolOper.exists || op == TlaBoolOper.forall || op == TlaOper.chooseBounded =>
        val sign =
          if (op == TlaBoolOper.exists)
            UTFPrinter.m_exists
          else if (op == TlaBoolOper.forall)
            UTFPrinter.m_forall
          else "CHOOSE "

        HovBox(
          TextElem("%s%s".format(sign, x)),
          TextElem(" %s ".format(UTFPrinter.m_in)),
          IndentBox(HovBox(
            toFormatElem(op.precedence, set),
            TextElem(": "),
            IndentBox(toFormatElem(op.precedence, pred))
          )) /////
        ) /////

      case OperEx(TlaSetOper.enumSet, args@_*) =>
        // a set enumeration, e.g., { 1, 2, 3 }
        HovBox(
          TextElem("{ "),
          IndentBox(HovBox(args.map(toFormatElem((0, 0), _)): _*).setSep(", ")),
          TextElem(" }")
        ) ////

      case OperEx(TlaFunOper.enum, keysAndValues@_*) =>
        // a record, e.g., [ x |-> 1, y |-> 2 ]
        val keys = keysAndValues.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = keysAndValues.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p =>
            HovBox(
              toFormatElem((0, 0), p._1),
              TextElem(" %s ".format(UTFPrinter.m_mapto)),
              toFormatElem((0, 0), p._2)
            )) ////

        HovBox(
          TextElem("["),
          IndentBox(
            HovBox(boxes: _*).setSep(", ")),
          TextElem("]")
        ) ////

      case OperEx(TlaFunOper.funDef, mapKeysAndValues@_*) =>
        val keys = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val mapEx = mapKeysAndValues.head
        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p =>
            HovBox(
              toFormatElem((0, 0), p._1),
              TextElem(" %s ".format(UTFPrinter.m_in)),
              toFormatElem((0, 0), p._2)))

        HovBox(TextElem("["),
          IndentBox(HovBox(boxes: _*).setSep(", ")),
          TextElem(" %s ".format(UTFPrinter.m_mapto)),
          toFormatElem((0, 0), mapEx),
          TextElem("]"))

      case OperEx(TlaSetOper.map, mapKeysAndValues@_*) =>
        val keys = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val mapEx = mapKeysAndValues.head
        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p =>
            HovBox(
              toFormatElem((0, 0), p._1),
              TextElem(" %s ".format(UTFPrinter.m_in)),
              toFormatElem((0, 0), p._2)))

        HovBox(TextElem("{"),
          IndentBox(HovBox(boxes: _*).setSep(", ")),
          TextElem(": "),
          toFormatElem((0, 0), mapEx),
          TextElem("}"))

      case OperEx(TlaFunOper.except, mapKeysAndValues@_*) =>
        val keys = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val mapEx = mapKeysAndValues.head

        def formatIndex(key: TlaEx) = key match {
          case OperEx(TlaFunOper.tuple, indices@_*) =>
            TextElem("!" + indices.map(s => s"[$s]").mkString(""))
          case _ =>
            throw new IllegalArgumentException("Expected a tuple as an EXCEPT index")
        }

        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p =>
            HovBox(
              formatIndex(p._1),
              TextElem(" = "),
              toFormatElem((0, 0), p._2)))

        HovBox(TextElem("["),
          toFormatElem((0, 0), mapEx),
          TextElem(" EXCEPT "),
          HBox(boxes: _*).setSep(", "),
          TextElem(" %s ".format(UTFPrinter.m_mapto)),
          toFormatElem((0, 0), mapEx),
          TextElem("]")
        ) /////

      case OperEx(TlaFunOper.app, funEx, argEx) =>
        HovBox(
          toFormatElem(TlaFunOper.app.precedence, funEx),
          HBox(
            TextElem("["),
            toFormatElem(TlaFunOper.app.precedence, argEx),
            TextElem("]")
          )) /////

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        HovBox(
          TextElem("IF"),
          IndentBox(toFormatElem((0, 0), pred)),
          TextElem("THEN"),
          IndentBox(toFormatElem((0, 0), thenEx)),
          TextElem("ELSE"),
          IndentBox(toFormatElem((0, 0), elseEx))
        ). /////
          setSep(" ")

      case OperEx(op, lhs, rhs) if binaryOps.contains(op) =>
        val elem = HovBox(
          toFormatElem(op.precedence, lhs),
          TextElem(" %s ".format(binaryOps(op))),
          toFormatElem(op.precedence, rhs))

        wrapWithParen(parentPrecedence, op.precedence, elem)

      case OperEx(op, arg) if unaryOps.contains(op) =>
        val elem = HBox(TextElem(unaryOps(op)), toFormatElem(op.precedence, arg))
        wrapWithParen(parentPrecedence, op.precedence, elem)

      case OperEx(op, args@_*) if funOps.contains(op) =>
        val elem =
          HovBox(
            TextElem("%s(".format(funOps(op))),
            HvBox(args.map(toFormatElem(op.precedence, _)): _*).setSep(", "),
            TextElem(")"))

        wrapWithParen(parentPrecedence, op.precedence, elem)

      case OperEx(op, args@_*) =>
        TextElem(expr.toString) // not perfect yet, but better than nothing
    }
  }

  private def wrapWithParen(parentPrecedence: (Int, Int), exprPrecedence: (Int, Int), el: FormatElem): FormatElem = {
    if (!(exprPrecedence._1 > parentPrecedence._2)) {
      // the expression precedence is not entirely to the right of its parent's precedence
      HBox(TextElem("("), el, TextElem(")"))
    } else {
      el // expression's precedence is higher, no need for parentheses
    }
  }

  class WindowWriter(writer: PrintWriter, val width: Int) {
    var cursorPos = 0
    var indent = 0
    var onNewLine = true

    def pushIndent(): Unit = indent += 2

    def popIndent(): Unit = indent -= 2

    def fitsOneLine(len: Int): Boolean = cursorPos + len <= width

    def print(text: String): Unit = {
      if (cursorPos >= width) {
        printlnOnce()
      }
      if (onNewLine) {
        writer.write(makeTab(indent))
      }
      writer.write(text)
      cursorPos += text.length
      onNewLine = false
    }

    def println(): Unit = {
      cursorPos = indent
      writer.println() // carriage return
      onNewLine = true
    }

    def printlnOnce(): Unit = {
      if (!onNewLine)
        println()
    }

    private def makeTab(indent: Int): String = {
      // indentation should not take over more than a half of the window
      val nspaces = Math.min(indent, width / 2)
      1 to nspaces map (_ => " ") mkString ""
    }
  }

  abstract class FormatElem() {
    def write(ww: WindowWriter): Unit

    def length: Int
  }

  case class TextElem(text: String) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      ww.print(text)
    }

    override def length: Int = text.length
  }

  case class HBox(elems: FormatElem*) extends FormatElem {
    /**
      * Element separator
      */
    var sep = ""

    def setSep(s: String): HBox = {
      sep = s
      this
    }

    override def write(ww: WindowWriter): Unit = {
      for ((el, no) <- elems.zipWithIndex) {
        if (no != 0) {
          ww.print(sep)
        }
        el.write(ww)
      }
    }

    override def length: Int = if (elems.isEmpty) 0 else (elems.size - 1) * sep.length + elems.map(_.length).sum
  }

  /**
    * A vertical box that places its elements in separate lines
    *
    * @param elems formatting elements
    */
  case class VBox(elems: FormatElem*) extends FormatElem {
    /**
      * the text to write in the beginning of each new line
      */
    var prefix = ""
    /**
      * The element separator
      */
    var sep = ""

    def setSep(s: String): VBox = {
      sep = s
      this
    }

    def setPrefix(p: String): VBox = {
      prefix = p
      this
    }

    override def write(ww: WindowWriter): Unit = {
      for ((el, no) <- elems.zipWithIndex) {
        if (no != 0) {
          ww.print(sep)
        }
        ww.printlnOnce()
        ww.print(prefix)
        ww.pushIndent()
        el.write(ww)
        ww.popIndent()
      }
    }

    override def length: Int = textWidth // the vertical box moves to the new line after printing the elements
  }

  /**
    * A formatting box that tries to squeeze its elements in one line. If this does not work, it becomes
    * a vertical box (VBox).
    *
    * @param elems formatting elements
    */
  case class HvBox(elems: FormatElem*) extends FormatElem {
    /**
      * The element separator
      */
    var sep = ""

    def setSep(s: String): HvBox = {
      sep = s
      this
    }

    override def write(ww: WindowWriter): Unit = {
      val wholeLen = length
      if (ww.fitsOneLine(wholeLen)) {
        HBox(elems: _*).setSep(sep).write(ww)
      } else {
        VBox(elems: _*).setSep(sep).write(ww)
      }
    }

    override def length: Int = if (elems.isEmpty) 0 else (elems.size - 1) * sep.length + elems.map(_.length).sum
  }

  /**
    * The box that fits as many elements as possible in the same line and arranges in the following lines the rest
    *
    * @param elems elements to arrange
    */
  case class HovBox(elems: FormatElem*) extends FormatElem {
    /**
      * The element separator
      */
    var sep = ""

    /**
      * if true, then the separator should be placed before line break; otherwise, it is placed after.
      */
    var isHangingSep = true

    def setSep(s: String): HovBox = {
      sep = s
      this
    }

    def setIsHangingSep(b: Boolean): HovBox = {
      isHangingSep = b
      this
    }

    override def write(ww: WindowWriter): Unit = {
      for ((el, no) <- elems.zipWithIndex) {
        val needSep = no != 0
        if (needSep && isHangingSep) {
          ww.print(sep) // the separator stays on the same line
        }
        val elLen = el.length + (if (needSep && !isHangingSep) sep.length else 0)
        if (!ww.fitsOneLine(elLen)) {
          ww.printlnOnce()
        }
        if (needSep && !isHangingSep) {
          ww.print(sep) // the separator starts on the next line
        }
        el.write(ww)
      }
    }

    override def length: Int = if (elems.isEmpty) 0 else (elems.size - 1) * sep.length + elems.map(_.length).sum
  }

  /**
    * A box that increases the indentation level. It only adds tabs after a line break.
    *
    * @param elem a formatting element to which indentation applies
    */
  case class IndentBox(elem: FormatElem) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      ww.pushIndent()
      elem.write(ww)
      ww.popIndent()
    }

    override def length: Int = elem.length
  }

}

object PrettyWriter {
  private val unaryOps = HashMap(
    TlaBoolOper.not -> "~",
    TlaArithOper.uminus -> "-",
    TlaSetOper.union -> "UNION ",
    TlaActionOper.enabled -> "ENABLED ",
    TlaActionOper.unchanged -> "UNCHANGED ",
    TlaFunOper.domain -> "DOMAIN "
  ) ////

  private val funOps = HashMap(
    TlaFiniteSetOper.cardinality -> "Cardinality",
    TlaFiniteSetOper.isFiniteSet -> "IsFiniteSet",
    TlaSeqOper.append -> "Append",
    TlaSeqOper.head -> "Head",
    TlaSeqOper.tail -> "Tail",
    TlaSeqOper.len -> "Len",
    TlaSetOper.seqSet -> "Seq"
  ) ////

  private val binaryOps =
    HashMap(TlaOper.eq -> "=",
      TlaOper.ne -> UTFPrinter.m_neq,
      TlaBoolOper.implies -> UTFPrinter.m_impl,
      TlaBoolOper.equiv -> UTFPrinter.m_equiv,
      TlaArithOper.plus -> "+",
      TlaArithOper.minus -> "-",
      TlaArithOper.mult -> "*",
      TlaArithOper.div -> "/",
      TlaArithOper.mod -> "%",
      TlaArithOper.realDiv -> "/.",
      TlaArithOper.exp -> "^",
      TlaArithOper.dotdot -> "..",
      TlaArithOper.lt -> "<",
      TlaArithOper.gt -> ">",
      TlaArithOper.le -> UTFPrinter.m_le,
      TlaArithOper.ge -> UTFPrinter.m_ge,
      TlaSetOper.in -> UTFPrinter.m_in,
      TlaSetOper.notin -> UTFPrinter.m_notin,
      TlaSetOper.cap -> UTFPrinter.m_cap,
      TlaSetOper.cup -> UTFPrinter.m_cup,
      TlaSetOper.setminus -> UTFPrinter.m_setminus,
      TlaSetOper.subseteq -> UTFPrinter.m_subseteq,
      TlaSetOper.subsetProper -> UTFPrinter.m_subset,
      TlaSetOper.supseteq -> UTFPrinter.m_supseteq,
      TlaSetOper.supsetProper -> UTFPrinter.m_supset,
      TlaActionOper.composition -> UTFPrinter.m_cdot,
      TlaSeqOper.concat -> UTFPrinter.m_ring,
      TlcOper.atat -> "@@",
      TlcOper.colonGreater -> ":>",
      BmcOper.withType -> "<:"
    ) ////
}
