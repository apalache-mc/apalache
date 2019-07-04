package at.forsyte.apalache.tla.lir.io

import java.io.PrintWriter

import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.io.PrettyWriter._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

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
    toFormatElem(expr).write(new WindowWriter(writer, textWidth))
  }

  def toFormatElem(expr: TlaEx): FormatElem = {
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
        val sign = if (op == TlaBoolOper.and) " /\\ " else " \\/ "
        VBox(args map toFormatElem, sign, "")

      case OperEx(op, x, set, pred)
        if op == TlaBoolOper.exists || op == TlaBoolOper.forall || op == TlaOper.chooseBounded =>
        val sign =
          if (op == TlaBoolOper.exists)
            UTFPrinter.m_exists
          else if (op == TlaBoolOper.forall)
            UTFPrinter.m_forall
          else "CHOOSE "

        val elems =
          TextElem("%s%s %s ".format(sign, x, UTFPrinter.m_in)) ::
            HvBox(Seq(toFormatElem(set), TextElem(": ")), "") ::
            HvBox(Seq(toFormatElem(pred)), "") :: Nil
        HvBox(elems, "")

      case OperEx(TlaSetOper.enumSet, args@_*) =>
        HovBox(TextElem("{") :: IndentBox(HovBox(args map toFormatElem, ", ")) :: TextElem("}") :: Nil, "")

      case OperEx(TlaFunOper.enum, keysAndValues@_*) =>
        val keys = keysAndValues.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = keysAndValues.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p => HovBox(Seq(toFormatElem(p._1), TextElem(UTFPrinter.m_mapto), toFormatElem(p._2)), ""))
        HovBox(TextElem("[") :: IndentBox(HBox(boxes, ", ")) :: TextElem("]") :: Nil, "")

      case OperEx(TlaFunOper.funDef, mapKeysAndValues@_*) =>
        val keys = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val mapEx = mapKeysAndValues.head
        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p => HovBox(
            Seq(toFormatElem(p._1), TextElem(" %s ".format(UTFPrinter.m_in)), toFormatElem(p._2)),
            ""))
        HovBox(TextElem("[") :: IndentBox(HovBox(boxes, ", "))
          :: TextElem(" %s ".format(UTFPrinter.m_mapto)) :: toFormatElem(mapEx) :: TextElem("]") :: Nil, "")

      case OperEx(TlaSetOper.map, mapKeysAndValues@_*) =>
        val keys = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val mapEx = mapKeysAndValues.head
        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p => HovBox(
            Seq(toFormatElem(p._1), TextElem(" %s ".format(UTFPrinter.m_in)), toFormatElem(p._2)),
            ""))
        HovBox(TextElem("{") :: IndentBox(HovBox(boxes, ", "))
          :: TextElem(": ") :: toFormatElem(mapEx) :: TextElem("}") :: Nil, "")

      case OperEx(TlaFunOper.except, mapKeysAndValues@_*) =>
        val keys = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 0) map (_._1)
        val values = mapKeysAndValues.tail.zipWithIndex filter (_._2 % 2 == 1) map (_._1)
        val mapEx = mapKeysAndValues.head
        def formatIndex(key: TlaEx) = key match {
          case OperEx(TlaFunOper.tuple, indices @ _*) =>
            TextElem("!" + indices.map(s => s"[$s]").mkString(""))
          case _ =>
            throw new IllegalArgumentException("Expected a tuple as an EXCEPT index")
        }
        val boxes: Seq[FormatElem] =
          keys.zip(values).map(p => HovBox(
            Seq(formatIndex(p._1), TextElem(" = "), toFormatElem(p._2)),
              ""))
        HovBox(TextElem("[") :: toFormatElem(mapEx) :: TextElem(" EXCEPT ")
          :: HBox(boxes, ", ")
          :: TextElem(" %s ".format(UTFPrinter.m_mapto)) :: toFormatElem(mapEx) :: TextElem("]") :: Nil, "")

      case OperEx(TlaFunOper.app, funEx, argEx) =>
        HovBox(Seq(toFormatElem(funEx), HBox(TextElem("[") :: toFormatElem(argEx) :: TextElem("]") :: Nil, "")), "")

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        HovBox(TextElem("IF") :: IndentBox(toFormatElem(pred))
          :: TextElem("THEN") :: IndentBox(toFormatElem(thenEx))
          :: TextElem("ELSE") :: IndentBox(toFormatElem(elseEx)) :: Nil, " ")

      case OperEx(op, lhs, rhs) if binaryOps.contains(op) =>
        HovBox(toFormatElem(lhs) :: TextElem(" %s ".format(binaryOps(op))) :: toFormatElem(rhs) :: Nil, "")

      case OperEx(op, arg) if unaryOps.contains(op) =>
        HBox(Seq(TextElem(unaryOps(op)), toFormatElem(arg)), "")

      case OperEx(op, args@_*) if funOps.contains(op) =>
        HovBox(TextElem("%s(".format(funOps(op))) :: HvBox(args map toFormatElem, ", ") :: TextElem(")") :: Nil, "")

      case OperEx(op, args@_*) =>
        TextElem(expr.toString) // not perfect yet, but better than nothing
    }
  }

  class WindowWriter(writer: PrintWriter, val width: Int) {
    var cursorPos = 0
    var indent = 0

    def pushIndent(): Unit = indent += 4

    def popIndent(): Unit = indent -= 4

    def fitsOneLine(len: Int): Boolean = cursorPos + len <= width

    def print(text: String): Unit = {
      writer.write(text)
      cursorPos += text.length
      if (cursorPos >= width) {
        println()
      }
    }

    def println(): Unit = {
      cursorPos = indent
      writer.println() // carriage return
      writer.write(makeTab(indent))
    }
  }

  abstract class FormatElem() {
    def write(ww: WindowWriter): Unit

    def len: Int
  }

  case class TextElem(text: String) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      ww.print(text)
    }

    override def len: Int = text.length
  }

  case class HBox(elems: Seq[FormatElem], sep: String) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      for ((el, no) <- elems.zipWithIndex) {
        if (no != 0) {
          ww.print(sep)
        }
        el.write(ww)
      }
    }

    override def len: Int = if (elems.isEmpty) 0 else (elems.size - 1) * sep.length + elems.map(_.len).sum
  }

  case class VBox(elems: Seq[FormatElem], prefix: String, sep: String) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      ww.pushIndent()
      for ((el, no) <- elems.zipWithIndex) {
        if (no != 0) {
          ww.print(sep)
          ww.println()
        }
        ww.print(prefix)
        el.write(ww)
      }
      ww.popIndent()
    }

    override def len: Int = textWidth // the vertical box moves to the new line after printing the elements
  }

  case class HvBox(elems: Seq[FormatElem], sep: String) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      val wholeLen = len
      if (ww.fitsOneLine(wholeLen)) {
        HBox(elems, sep).write(ww)
      } else {
        VBox(elems, prefix = "", sep).write(ww)
      }
    }

    override def len: Int = if (elems.isEmpty) 0 else (elems.size - 1) * sep.length + elems.map(_.len).sum
  }

  case class HovBox(elems: Seq[FormatElem], sep: String) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      for ((el, no) <- elems.zipWithIndex) {
        val elLen = el.len
        if (no != 0) {
          ww.print(sep)
        }
        if (!ww.fitsOneLine(elLen)) {
          ww.println()
        }
        el.write(ww)
      }
    }

    override def len: Int = if (elems.isEmpty) 0 else (elems.size - 1) * sep.length + elems.map(_.len).sum
  }

  case class IndentBox(elem: FormatElem) extends FormatElem {
    override def write(ww: WindowWriter): Unit = {
      ww.pushIndent()
      elem.write(ww)
      ww.popIndent()
    }

    override def len: Int = elem.len
  }

  private def makeTab(indent: Int): String = 1 to indent map (_ => " ") mkString ""
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
