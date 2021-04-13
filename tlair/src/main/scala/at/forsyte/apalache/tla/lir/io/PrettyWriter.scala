package at.forsyte.apalache.tla.lir.io

import java.io.{File, FileWriter, PrintWriter}

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlcOper, _}
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._
import org.bitbucket.inkytonik.kiama.output.PrettyPrinter

import at.forsyte.apalache.tla.lir.UntypedPredefs._

import scala.collection.immutable.HashMap

/**
 * <p>A pretty printer to a file that formats a TLA+ expression to a given text width (normally, 80 characters).
 * As pretty-printing is hard, we are using the kiama library for finding an optimal layout.
 * Note that this printer is not using UTF8 characters, as its output should be readable by TLA+ Tools.</p>
 *
 * <p>Finding a nice code layout is hard. In many cases, it is also a matter of taste. To see the examples
 * of formatting, check TestPrettyWriter.</p>
 *
 * <p>TODO: Parameterize PrettyWriter by a Printer that would give us access to different graphical representations
 * of TLA+ expressions, e.g., UTFPrinter. </p>
 *
 * @author Igor Konnov
 */
class PrettyWriter(writer: PrintWriter, textWidth: Int = 80, indent: Int = 2) extends PrettyPrinter with TlaWriter {
  override val defaultIndent: Int = indent

  val REC_FUN_UNDEFINED = "recFunNameUndefined"
  // when printing a recursive function, this variable contains its name
  private var recFunName: String = REC_FUN_UNDEFINED
  // the stack of lambda declarations
  private var lambdaStack: List[TlaOperDecl] = Nil

  private def prettyWriteDoc(doc: Doc): Unit = writer.write(pretty(doc, textWidth).layout)

  def write(mod: TlaModule): Unit = prettyWriteDoc(toDoc(mod))

  // Declarations have a trailing empty line
  def write(decl: TlaDecl): Unit = prettyWriteDoc(toDoc(decl) <> line <> line)

  def write(expr: TlaEx): Unit = prettyWriteDoc(toDoc((0, 0), expr))

  def writeComment(commentStr: String): Unit = prettyWriteDoc(toComment(commentStr))

  def writeHeader(moduleName: String, extensionModuleNames: List[TlaModule] = List.empty): Unit =
    prettyWriteDoc(
        moduleNameDoc(moduleName) <> moduleExtendsDoc(extensionModuleNames) <> line
    )

  def writeFooter(): Unit = prettyWriteDoc(moduleTerminalDoc)

  private def toComment(commentStr: String): Doc = text(s"(* $commentStr *)") <> line

  private def moduleNameDoc(name: String): Doc = {
    val middle = s" MODULE $name "
    val nDashes = math.max(5, (textWidth - middle.length) / 2) // int div rounds down
    s"${List.fill(nDashes)("-").mkString}$middle${List.fill(nDashes)("-").mkString}" <> line
  }

  private def moduleExtendsDoc(moduleNames: List[TlaModule]): Doc =
    if (moduleNames.isEmpty) emptyDoc
    else line <> text(s"EXTENDS ${moduleNames.map(_.name).mkString(", ")}") <> line

  private def moduleTerminalDoc: Doc =
    s"${List.fill(textWidth)("=").mkString}" <> line

  def toDoc(mod: TlaModule, extensionModuleNames: List[TlaModule] = List.empty): Doc = {
    moduleNameDoc(mod.name) <>
      moduleExtendsDoc(extensionModuleNames) <>
      lsep((mod.declarations.toList map toDoc) :+ moduleTerminalDoc, line)
  }

  def toDoc(parentPrecedence: (Int, Int), expr: TlaEx): Doc = {
    expr match {
      case NameEx(x) if x == "LAMBDA" =>
        // this is reference to the lambda expression that was introduced ealier
        lambdaStack match {
          case Nil =>
            throw new IllegalStateException("Expected LAMBDA to be introduced earlier")

          case top :: _ =>
            val paramsDoc =
              if (top.formalParams.isEmpty)
                text("")
              else
                ssep(top.formalParams map toDoc, "," <> softline)

            group(
                "LAMBDA" <> space <> paramsDoc <> text(":") <> space <>
                  toDoc((0, 0), top.body))
        }

      case NameEx(x) =>
        text(x)

      case ValEx(TlaStr(str))   => text("\"%s\"".format(str))
      case ValEx(TlaInt(value)) => text(value.toString)
      case ValEx(TlaBool(b))    => text(if (b) "TRUE" else "FALSE")
      case ValEx(TlaBoolSet)    => text("BOOLEAN")
      case ValEx(TlaIntSet)     => text("Int")
      case ValEx(TlaNatSet)     => text("Nat")
      case ValEx(TlaRealSet)    => text("Real")
      case ValEx(TlaStrSet)     => text("STRING")

      case NullEx => text("\"NOP\"")

      case OperEx(op @ TlaActionOper.prime, e) =>
        toDoc(op.precedence, e) <> "'"

      case OperEx(TlaSetOper.enumSet) =>
        // an empty set
        text("{}")

      case OperEx(op @ TlaSetOper.enumSet, arg) =>
        // a singleton set
        group("{" <> toDoc(op.precedence, arg) <> "}")

      case OperEx(op @ TlaSetOper.enumSet, args @ _*) =>
        // a set enumeration, e.g., { 1, 2, 3 }
        val argDocs = args.map(toDoc(op.precedence, _))
        val commaSeparated = folddoc(argDocs.toList, _ <> text(",") <@> _)
        group(braces(group(softline <> nest(commaSeparated, indent)) <> softline))

      case OperEx(op @ TlaFunOper.tuple, args @ _*) =>
        // a tuple, e.g., <<1, 2, 3>>
        val argDocs = args.map(toDoc(op.precedence, _))
        val commaSeparated = ssep(argDocs.toList, text(",") <> softline)
        group(text("<<") <> nest(linebreak <> commaSeparated, indent) <> linebreak <> ">>")

      case OperEx(op, args @ _*) if op == TlaBoolOper.and || op == TlaBoolOper.or =>
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
              group(doc) // prefer a horizontal layout
            } else {
              val doc = nest(folddoc(argDocs, _ <> linebreak <> sign <> space <> _))
              doc // prefer a vertical layout, here we could use the indented form
            }
          wrapWithParen(parentPrecedence, op.precedence, grouped)
        }

      case OperEx(op, x, set, pred)
          if op == TlaBoolOper.exists || op == TlaBoolOper.forall || op == TlaOper.chooseBounded =>
        val sign = PrettyWriter.bindingOps(op)
        val doc =
          group(
              group(
                  text(sign) <> space <> text(x.toString) <> space <>
                    text(PrettyWriter.binaryOps(TlaSetOper.in)) <> softline <>
                    toDoc(op.precedence, set) <> text(":")) <>
                nest(line <> toDoc(op.precedence, pred))
          ) ///

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, x, pred) if op == TlaTempOper.EE || op == TlaTempOper.AA =>
        val sign = PrettyWriter.bindingOps(op)
        val doc =
          group(
              group(text(sign) <> space <> text(x.toString) <> ":") <>
                nest(line <> toDoc(op.precedence, pred))
          ) ///

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(TlaFunOper.enum, keysAndValues @ _*) =>
        // a record, e.g., [ x |-> 1, y |-> 2 ]
        val (ks, vs) = keysAndValues.zipWithIndex partition (_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k |-> v
        val boxes =
          keys.zip(values).map(p => group(strNoQuotes(p._1) <> space <> "|->" <> nest(line <> toDoc((0, 0), p._2)))) ///

        group(brackets(nest(ssep(boxes.toList, comma <> line))))

      case OperEx(TlaSetOper.recSet, keysAndValues @ _*) =>
        // a record, e.g., [ x: S, y: T ]
        val (ks, vs) = keysAndValues.zipWithIndex partition (_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k: v
        val boxes =
          keys.zip(values).map(p => group(strNoQuotes(p._1) <> ":" <> nest(line <> toDoc((0, 0), p._2)))) ///

        group(brackets(nest(ssep(boxes.toList, comma <> line))))

      case OperEx(TlaFunOper.funDef, body, keysAndValues @ _*) =>
        val (ks, vs) = keysAndValues.zipWithIndex partition (_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k \in v
        val boxes =
          keys
            .zip(values)
            .map(p => group(toDoc((0, 0), p._1) <> space <> "\\in" <> nest(line <> toDoc((0, 0), p._2)))) ///

        val binders = ssep(boxes.toList, comma <> line)
        val bodyDoc = toDoc((0, 0), body)
        group(
            text("[") <>
              nest(line <> binders <> space <> "|->" <> nest(line <> bodyDoc)) <> line <>
              text("]")
        ) ////

      case OperEx(TlaSetOper.map, body, keysAndValues @ _*) =>
        val (ks, vs) = keysAndValues.zipWithIndex partition (_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k |-> v
        val boxes =
          keys
            .zip(values)
            .map(p =>
              group(toDoc(TlaSetOper.in.precedence, p._1) <> space <>
                    "\\in" <> nest(line <> toDoc(TlaSetOper.in.precedence, p._2)))
            ) ///

        val binders = ssep(boxes.toList, comma <> line)
        val bodyDoc = toDoc((0, 0), body)
        group(braces(nest(line <> bodyDoc <> text(":") <> nest(line <> binders)) <> line))

      case OperEx(TlaSetOper.filter, name, set, pred) =>
        val binding = group(
            toDoc(TlaSetOper.in.precedence, name) <> softline <> "\\in" <>
              nest(line <> toDoc(TlaSetOper.in.precedence, set))
        ) ///
        // use the precedence (0, 0), as there is no need for parentheses around the predicate
        val filter = toDoc((0, 0), pred)
        group(
            text("{") <> nest(line <> binding <> ":" <> nest(line <> filter)) <> line <> text("}")
        ) ///

      // a function of multiple arguments that are packed into a tuple: don't print the angular brackets <<...>>
      case OperEx(op @ TlaFunOper.app, funEx, OperEx(TlaFunOper.tuple, args @ _*)) =>
        val argDocs = args.map(toDoc(op.precedence, _))
        val commaSeparatedArgs = folddoc(argDocs.toList, _ <> text(",") <@> _)
        group(
            toDoc(TlaFunOper.app.precedence, funEx) <> brackets(commaSeparatedArgs)
        ) ///

      // a function of a single argument
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        group(
            toDoc(TlaFunOper.app.precedence, funEx) <>
              text("[") <> nest(linebreak <> toDoc(TlaFunOper.app.precedence, argEx)) <> linebreak <> text("]")
        ) ///

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        val prec = TlaControlOper.ifThenElse.precedence
        val doc =
          group(
              text("IF") <> space <> toDoc(prec, pred) <> line <>
                text("THEN") <> space <> toDoc(prec, thenEx) <> line <>
                text("ELSE") <> space <> toDoc(prec, elseEx)
          ) ///

        wrapWithParen(parentPrecedence, prec, doc)

      case OperEx(TlaControlOper.caseWithOther, otherEx, guardsAndUpdates @ _*) =>
        val prec = TlaControlOper.caseWithOther.precedence
        val (gs, us) = guardsAndUpdates.zipWithIndex partition (_._2 % 2 == 0)
        val (guards, updates) = (gs.map(_._1), us.map(_._1))
        // format each guard-update pair (g, u) into ![g] = u
        val pairs =
          guards
            .zip(updates)
            .map(p =>
              group(toDoc(prec, p._1) <>
                    nest(line <> text("->") <> space <> toDoc(prec, p._2)))
            ) ///

        val pairsWithOther =
          if (otherEx == NullEx) {
            pairs
          } else {
            pairs :+ group("OTHER" <> nest(line <> "->" <> space <> toDoc(prec, otherEx)))
          }

        val doc = group(text("CASE") <> nest(space <> folddoc(pairsWithOther.toList, _ <> line <> "[]" <> space <> _)))
        wrapWithParen(parentPrecedence, prec, doc)

      case opex @ OperEx(TlaControlOper.caseNoOther, guardsAndUpdates @ _*) =>
        // delegate this case to CASE with OTHER by passing NullEx
        toDoc(parentPrecedence, OperEx(TlaControlOper.caseWithOther, NullEx +: guardsAndUpdates: _*)(opex.typeTag))

      case OperEx(TlaFunOper.except, funEx, keysAndValues @ _*) =>
        val (ks, vs) = keysAndValues.zipWithIndex partition (_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into ![k] = v
        val boxes =
          keys
            .zip(values)
            .map(p =>
              group(text("!") <> brackets(toDoc((0, 0), p._1)) <> space <> text("=") <>
                    nest(line <> toDoc((0, 0), p._2)))
            ) ///

        val updates = ssep(boxes.toList, comma <> line)

        val doc =
          text("[") <> nest(line <> toDoc(TlaFunOper.except.precedence, funEx) <>
                nest(softline <> text("EXCEPT") <> line <> updates)) <> line <>
            text("]")

        group(doc)

      // a set of functions [S -> T]
      case OperEx(TlaSetOper.funSet, domain, coDomain) =>
        val doc =
          toDoc(TlaSetOper.funSet.precedence, domain) <>
            nest(
                line <>
                  text("->") <> space <>
                  toDoc(TlaSetOper.funSet.precedence, coDomain))
        group(brackets(doc))

      // a labelled expression L3(a, b) :: 42
      case expr @ OperEx(oper @ TlaOper.label, decoratedExpr, ValEx(TlaStr(name)), args @ _*) =>
        val argDocs = args map {
          case ValEx(TlaStr(str)) => text(str)
          case _                  => throw new MalformedTlaError("Malformed expression", expr)
        }
        val optionalArgs =
          if (args.isEmpty)
            emptyDoc
          else
            parens(ssep(argDocs.toList, text(",") <> softline))

        val doc =
          text(name) <> optionalArgs <> space <> "::" <>
            nest(line <> toDoc(oper.precedence, decoratedExpr))
        group(wrapWithParen(parentPrecedence, oper.precedence, doc))

      // [A]_vars or <A>_vars
      case OperEx(op, action, vars) if op == TlaActionOper.stutter || op == TlaActionOper.nostutter =>
        def wrapper = if (op == TlaActionOper.stutter) brackets _ else angles _

        val doc =
          wrapper(toDoc(op.precedence, action)) <>
            "_" <> toDoc(op.precedence, vars)
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      case OperEx(op, vars, action) if op == TlaTempOper.weakFairness || op == TlaTempOper.strongFairness =>
        val sign = if (op == TlaTempOper.weakFairness) "WF" else "SF"
        val doc =
          sign <> "_" <> toDoc(op.precedence, vars) <>
            parens(toDoc(op.precedence, action))
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      case OperEx(op, arg @ NameEx(_)) if PrettyWriter.unaryOps.contains(op) =>
        val doc = text(PrettyWriter.unaryOps(op)) <> toDoc(op.precedence, arg)
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, arg @ ValEx(_)) if PrettyWriter.unaryOps.contains(op) =>
        val doc = text(PrettyWriter.unaryOps(op)) <> toDoc(op.precedence, arg)
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, arg @ OperEx(_, _)) if PrettyWriter.unaryOps.contains(op) =>
        // a unary operator over unary operator, no parentheses needed
        val doc = text(PrettyWriter.unaryOps(op)) <> toDoc(op.precedence, arg)
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(TlaFunOper.recFunRef) =>
        text(recFunName) // even if the name is undefined, print it

      case OperEx(op, arg) if PrettyWriter.unaryOps.contains(op) =>
        // in all other cases, introduce parentheses.
        // Yse the minimal precedence, as we are introducing the parentheses in any case.
        text(PrettyWriter.unaryOps(op)) <> parens(toDoc((0, 0), arg))

      case OperEx(op, lhs, rhs) if PrettyWriter.binaryOps.contains(op) =>
        val doc =
          toDoc(op.precedence, lhs) <>
            nest(
                line <>
                  text(PrettyWriter.binaryOps(op)) <> space <>
                  toDoc(op.precedence, rhs))
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      case OperEx(op, args @ _*) if PrettyWriter.naryOps.contains(op) =>
        val sign = PrettyWriter.naryOps(op)
        val argDocs = args.map(toDoc(op.precedence, _)).toList
        val doc = nest(folddoc(argDocs, _ <> line <> sign <> space <> _))
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      case OperEx(op @ TlaOper.apply, NameEx(name), args @ _*) =>
        // apply an operator by its name, e.g., F(x)
        val argDocs = args.map(toDoc(op.precedence, _)).toList
        val commaSeparated = ssep(argDocs, "," <> softline)
        val doc =
          if (args.isEmpty) {
            text(name)
          } else {
            group(name <> parens(commaSeparated))
          }

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op @ TlaOper.apply, operEx, args @ _*) =>
        // apply an operator by its definition, e.g., (LAMBDA x: x)(y)
        val argDocs = args.map(toDoc(op.precedence, _)).toList
        val commaSeparated = ssep(argDocs, "," <> softline)
        val doc = group(parens(toDoc((0, 0), operEx)) <> parens(commaSeparated))

        wrapWithParen(parentPrecedence, op.precedence, doc)

      // TODO: fix funSet
      case OperEx(op, args @ _*) =>
        val argDocs = args.map(toDoc(op.precedence, _)).toList
        val commaSeparated = ssep(argDocs, "," <> softline)
        val doc =
          if (args.isEmpty) {
            text(op.name)
          } else {
            group(op.name <> parens(commaSeparated))
          }

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case LetInEx(body, d @ TlaOperDecl("LAMBDA", _, _)) =>
        // save the declaration and unpack it later, when NameEx(LAMBDA) is met
        lambdaStack = d :: lambdaStack // push the lambda definition on the top
        val doc = toDoc((0, 0), body)
        lambdaStack = lambdaStack.tail // pop the lambda definition
        doc

      case LetInEx(body, decls @ _*) =>
        def eachDecl(d: TlaOperDecl) = {
          group("LET" <> space <> toDoc(d) <> line <> "IN")
        }

        group(ssep(decls.map(eachDecl).toList, line) <>
              line <> toDoc((0, 0), body))
    }
  }

  def toDoc(decl: TlaDecl): Doc = {
    decl match {
      case TlaConstDecl(name) =>
        group("CONSTANT" <> space <> name)

      case TlaVarDecl(name) =>
        group("VARIABLE" <> space <> name)

      case TlaAssumeDecl(body) =>
        group("ASSUME" <> parens(toDoc((0, 0), body)))

      // a declaration of a recursive function
      case TlaOperDecl(name, List(), OperEx(TlaFunOper.recFunDef, body, keysAndValues @ _*)) =>
        val (ks, vs) = keysAndValues.zipWithIndex partition (_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k \in v
        val boxes =
          keys
            .zip(values)
            .map(p => group(toDoc((0, 0), p._1) <> space <> "\\in" <> nest(line <> toDoc((0, 0), p._2)))) ///

        val binders = ssep(boxes.toList, comma <> line)

        // set the name of the recursive function. TLA+ forbids mutual recursion, so we do not need a stack
        recFunName = name
        // [x \in S]
        val binding = brackets(binders)
        // f[x \in S] == e
        val doc = group(name <> binding <> space <> "==" <> space <> toDoc((0, 0), body))
        recFunName = REC_FUN_UNDEFINED
        doc

      // an operator declaration (may be recursive)
      case tod @ TlaOperDecl(name, params, body) =>
        val recPreambule =
          if (!tod.isRecursive)
            text("")
          else
            "RECURSIVE" <> space <> toDoc(OperParam(name, params.length)) <> line

        val paramsDoc =
          if (params.isEmpty)
            text("")
          else parens(ssep(params map toDoc, "," <> softline))

        recPreambule <> group(name <> paramsDoc <> space <> "==" <> nest(line <> toDoc((0, 0), body)))
    }
  }

  private def toDoc(param: OperParam): Doc = {
    if (param.isOperator) {
      group(param.name <> parens(ssep(List.fill(param.arity)("_"), "," <> softline)))
    } else {
      param.name
    }
  }

  private def wrapWithParen(parentPrecedence: (Int, Int), exprPrecedence: (Int, Int), doc: Doc): Doc = {
    // An expression has to be wrapped with parentheses if:
    //  1. The expression precedence is not entirely to the right of its parent's precedence, and
    //  2. The parent's precedence is not (0, 0). That is, (0, 0) consumes (0, 0).
    if (!(exprPrecedence._1 > parentPrecedence._2) && parentPrecedence != (0, 0)) {
      // the expression precedence is not entirely to the right of its parent's precedence
      parens(doc)
    } else {
      doc // expression's precedence is higher, no need for parentheses
    }
  }

  private def strNoQuotes(ex: TlaEx): String = {
    ex match {
      case ValEx(TlaStr(s)) => s
      case _                => throw new IllegalStateException("Expected a string as a record key, found: " + ex)
    }
  }

  def close(): Unit = writer.close()
}

object PrettyWriter {

  /**
   * Write a module to a file (without appending).
   *
   * @param module     a TLA module
   * @param outputFile an output file that will be created or overwritten
   */
  def write(module: TlaModule, outputFile: File): Unit = {
    val writer = new PrintWriter(new FileWriter(outputFile, false))
    try {
      new PrettyWriter(writer).write(module)
    } finally {
      writer.close()
    }
  }

  protected val unaryOps = HashMap(
      TlaBoolOper.not -> "~",
      TlaArithOper.uminus -> "-",
      TlaSetOper.union -> "UNION ",
      TlaSetOper.powerset -> "SUBSET ",
      TlaActionOper.enabled -> "ENABLED ",
      TlaActionOper.unchanged -> "UNCHANGED ",
      TlaFunOper.domain -> "DOMAIN ",
      TlaTempOper.box -> "[]",
      TlaTempOper.diamond -> "<>"
  ) ////

  protected val binaryOps =
    HashMap(
        TlaOper.eq -> "=",
        TlaOper.ne -> "/=",
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
        TlaArithOper.le -> "<=",
        TlaArithOper.ge -> ">=",
        TlaSetOper.in -> "\\in",
        TlaSetOper.notin -> "\\notin",
        TlaSetOper.cap -> "\\intersect",
        TlaSetOper.cup -> "\\union",
        TlaSetOper.setminus -> "\\",
        TlaSetOper.subseteq -> "\\subseteq",
        TlaActionOper.composition -> "\\cdot",
        TlaTempOper.leadsTo -> "~>",
        TlaTempOper.guarantees -> "-+->",
        TlaSeqOper.concat -> "\\o",
        TlcOper.colonGreater -> ":>",
        ApalacheOper.assign -> ":="
    ) ////

  protected val naryOps: Map[TlaOper, String] = HashMap(
      TlaSetOper.times -> "\\X",
      TlcOper.atat -> "@@"
  ) ////

  protected val bindingOps = HashMap(
      TlaBoolOper.exists -> "\\E",
      TlaBoolOper.forall -> "\\A",
      TlaOper.chooseBounded -> "CHOOSE",
      TlaTempOper.EE -> "\\EE",
      TlaTempOper.AA -> "\\AA"
  ) ////
}
