package at.forsyte.apalache.tla.lir.io

import java.io.PrintWriter

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import org.bitbucket.inkytonik.kiama.output.PrettyPrinter

import scala.collection.immutable.HashMap

/**
  * <p>A pretty printer to a file that formats a TLA+ expression to a given text width (normally, 80 characters).
  * As pretty-printing is hard, we are using the kiama library for finding an optimal layout.</p>
  *
  * @author Igor Konnov
  */
class PrettyWriter(writer: PrintWriter, textWidth: Int = 80, indent: Int = 2) extends PrettyPrinter {
  override val defaultIndent: Int = indent

  def write(expr: TlaEx): Unit = {
    writer.write(pretty(toDoc((0, 0), expr), textWidth).layout)
  }

  def toDoc(parentPrecedence: (Int, Int), expr: TlaEx): Doc = {
    // TODO: some operators are still calling UTFPrinter, fix it
    expr match {
      case NameEx(x) => text(x)

      case ValEx(TlaStr(str)) => text("\"%s\"".format(str))
      case ValEx(TlaInt(value)) => text(value.toString)
      case ValEx(TlaBool(b)) => text(if (b) "TRUE" else "FALSE")
      case ValEx(TlaBoolSet) => text("BOOLEAN")
      case ValEx(TlaIntSet) => text("Int")
      case ValEx(TlaNatSet) => text("Nat")
      case ValEx(TlaRealSet) => text("Real")
      case ValEx(TlaStrSet) => text("STRING")

      case OperEx(TlaSetOper.enumSet, args@_*) =>
        // a set enumeration, e.g., { 1, 2, 3 }
        val argDocs = args.map(toDoc((0, 0), _))
        val commaSeparated = ssep(argDocs.toList, text(",") <> softline)
        group(text("{") <> nest(line <> commaSeparated, indent) <> line <> "}")

      case OperEx(op, args@_*) if op == TlaBoolOper.and || op == TlaBoolOper.or =>
        // we are not using indented /\ and \/, as they are hard to get automatically
        val sign = if (op == TlaBoolOper.and) "/\\" else "\\/"

        if (args.isEmpty) {
          val const = tla.bool(op == TlaBoolOper.and)
          toDoc(parentPrecedence, const)
        } else {
          val argDocs = args.map(toDoc(op.precedence, _)).toList
          val grouped =
            if (argDocs.length <= 3) {
              val doc = nest(folddoc(argDocs, _ <> line <> sign <> space <> _))
              group(hang(doc)) // prefer a horizontal layout
            } else {
              val doc = nest(folddoc(argDocs, _ <> linebreak <> sign <> space <> _))
              doc              // prefer a vertical layout, here we could use the indented form
            }
          wrapWithParen(parentPrecedence, op.precedence, grouped)
        }

      case OperEx(op, x, set, pred)
        if op == TlaBoolOper.exists || op == TlaBoolOper.forall || op == TlaOper.chooseBounded =>
        val sign = PrettyWriter.bindingOps(op)
        group(
          group(text(sign) <> text(x.toString) <> space <>
            text(PrettyWriter.binaryOps(TlaSetOper.in)) <> softline <>
            toDoc(op.precedence, set) <> text(":")
          ) <>
            nest(line <> toDoc(op.precedence, pred))
        ) ///

      case OperEx(TlaFunOper.enum, keysAndValues@_*) =>
        // a record, e.g., [ x |-> 1, y |-> 2 ]
        val (ks, vs) = keysAndValues.zipWithIndex partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k |-> v
        val boxes =
          keys.zip(values).map(p =>
            group(toDoc((0, 0), p._1) <> space <> UTFPrinter.m_mapto <> nest(line <> toDoc((0, 0), p._2)))
          ) ///

        group(brackets(nest(ssep(boxes.toList, comma <> line))))

      case OperEx(TlaFunOper.funDef, body, keysAndValues@_*) =>
        val (ks, vs) = keysAndValues.zipWithIndex partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k \in v
        val boxes =
          keys.zip(values).map(p =>
            group(toDoc((0, 0), p._1) <> space <> UTFPrinter.m_in <> nest(line <> toDoc((0, 0), p._2)))
          ) ///

        val binders = ssep(boxes.toList, comma <> line)
        val bodyDoc = toDoc((0, 0), body)
        group(
          text("[") <>
          nest(line <> binders <> space <> UTFPrinter.m_mapto <> nest(line <> bodyDoc)) <> line <>
          text("]")
        ) ////

      case OperEx(TlaSetOper.map, body, keysAndValues@_*) =>
        val (ks, vs) = keysAndValues.zipWithIndex partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k |-> v
        val boxes =
          keys.zip(values).map(p =>
            group(toDoc((0, 0), p._1) <> space <> UTFPrinter.m_in <> nest(line <> toDoc((0, 0), p._2)))
          ) ///

        val binders = ssep(boxes.toList, comma <> line)
        val bodyDoc = toDoc((0, 0), body)
        group(braces(nest(line <> bodyDoc <> text(":") <> nest(line <> binders)) <> line))

      case OperEx(TlaFunOper.app, funEx, argEx) =>
        group(
          toDoc(TlaFunOper.app.precedence, funEx) <>
            text("[") <> nest(linebreak <> toDoc(TlaFunOper.app.precedence, argEx)) <> linebreak <> text("]")
        ) ///

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        val prec = TlaControlOper.ifThenElse.precedence
        group(
          text("IF") <> space <> toDoc(prec, pred) <> line <>
          text("THEN") <> space <> toDoc(prec, thenEx) <> line <>
          text("ELSE") <> space <> toDoc(prec, elseEx)
        ) ///

    case OperEx(TlaFunOper.except, funEx, keysAndValues@_*) =>
      val (ks, vs) = keysAndValues.zipWithIndex partition(_._2 % 2 == 0)
      val (keys, values) = (ks.map(_._1), vs.map(_._1))
      // format each key-value pair (k, v) into ![k] = v
      val boxes =
        keys.zip(values).map(p =>
          group(text("!") <> brackets(toDoc((0, 0), p._1)) <> space <> text("=") <>
            nest(line <> toDoc((0, 0), p._2)))
        ) ///

      val updates = ssep(boxes.toList, comma <> line)

      val doc =
        text("[") <> nest(line <> toDoc(TlaFunOper.except.precedence, funEx) <>
          nest(softline <> text("EXCEPT") <> line <> updates)) <> line <>
          text("]")

      group(doc)

      case OperEx(op, lhs, rhs) if PrettyWriter.binaryOps.contains(op) =>
        val doc =
          toDoc(op.precedence, lhs) <> line <>
            text(PrettyWriter.binaryOps(op)) <> space <>
            toDoc(op.precedence, rhs)
        wrapWithParen(parentPrecedence, op.precedence, group(hang(doc)))

      case OperEx(op, arg) if PrettyWriter.unaryOps.contains(op) =>
        val doc = text(PrettyWriter.unaryOps(op)) <> toDoc(op.precedence, arg)
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, args@_*) if PrettyWriter.funOps.contains(op) =>
        val doc = text(PrettyWriter.funOps(op)) <>
          parens(ssep(args.map(toDoc(op.precedence, _)).toList, comma))
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, args@_*) =>
        text(expr.toString) // not perfect yet, but better than nothing
    }
  }

  private def wrapWithParen(parentPrecedence: (Int, Int), exprPrecedence: (Int, Int), doc: Doc): Doc = {
    if (!(exprPrecedence._1 > parentPrecedence._2)) {
      // the expression precedence is not entirely to the right of its parent's precedence
      parens(doc)
    } else {
      doc // expression's precedence is higher, no need for parentheses
    }
  }
}

object PrettyWriter {
  protected val unaryOps = HashMap(
    TlaBoolOper.not -> UTFPrinter.m_not,
    TlaArithOper.uminus -> "-",
    TlaSetOper.union -> "UNION ",
    TlaActionOper.enabled -> "ENABLED ",
    TlaActionOper.unchanged -> "UNCHANGED ",
    TlaFunOper.domain -> "DOMAIN "
  ) ////

  protected val funOps = HashMap(
    TlaFiniteSetOper.cardinality -> "Cardinality",
    TlaFiniteSetOper.isFiniteSet -> "IsFiniteSet",
    TlaSeqOper.append -> "Append",
    TlaSeqOper.head -> "Head",
    TlaSeqOper.tail -> "Tail",
    TlaSeqOper.len -> "Len",
    TlaSetOper.seqSet -> "Seq"
  ) ////

  protected val binaryOps =
    HashMap(TlaOper.eq -> "=",
      TlaOper.ne -> UTFPrinter.m_neq,
      TlaBoolOper.implies -> "=>",
      TlaBoolOper.equiv -> "<=>",
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

  protected val bindingOps = HashMap(
    TlaBoolOper.exists -> UTFPrinter.m_exists,
    TlaBoolOper.forall -> UTFPrinter.m_forall,
    TlaOper.chooseBounded -> "CHOOSE"
  ) ////
}
