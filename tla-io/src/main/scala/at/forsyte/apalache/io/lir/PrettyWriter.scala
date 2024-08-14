package at.forsyte.apalache.io.lir

import at.forsyte.apalache.io.PrettyPrinterError
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import org.bitbucket.inkytonik.kiama.output.PrettyPrinter

import java.io.{File, FileWriter, PrintWriter}
import scala.collection.immutable.{HashMap, HashSet}
import java.io.StringWriter

/**
 * <p>A pretty printer to a file that formats a TLA+ expression to a given text width (normally, 80 characters). As
 * pretty-printing is hard, we are using the kiama library for finding an optimal layout. Note that this printer is not
 * using UTF8 characters, as its output should be readable by TLA+ Tools.</p>
 *
 * <p>Finding a nice code layout is hard. In many cases, it is also a matter of taste. To see the examples of
 * formatting, check TestPrettyWriter.</p>
 *
 * <p>TODO: Parameterize PrettyWriter by a Printer that would give us access to different graphical representations of
 * TLA+ expressions, e.g., UTFPrinter. </p>
 *
 * @author
 *   Igor Konnov
 */
class PrettyWriter(
    writer: PrintWriter,
    layout: TextLayout = new TextLayout,
    declAnnotator: TlaDeclAnnotator = new TlaDeclAnnotator)
    extends PrettyPrinter with TlaWriter {
  override val defaultIndent: Int = layout.indent

  val REC_FUN_UNDEFINED = "recFunNameUndefined"
  // when printing a recursive function, this variable contains its name
  private var recFunName: String = REC_FUN_UNDEFINED
  // the stack of lambda declarations
  private var lambdaStack: List[TlaOperDecl] = Nil

  private def prettyWriteDoc(doc: Doc): Unit = writer.write(pretty(doc, layout.textWidth).layout)

  def write(mod: TlaModule, extendedModuleNames: List[String] = List.empty): Unit =
    prettyWriteDoc(modToDoc(mod, extendedModuleNames))

  /**
   * Pretty-prints the given decl twice: Once as valid TLA, and once (before the TLA expression) in a comment, where
   * names of NameExs are replaced by their mapping in the nameReplacementMap. The output looks, for example, like this:
   *
   * {{{
   *  (* State0 ==
   *    ♢(x = 11) = FALSE
   * /\ ♢(x = 11)_unroll = FALSE *)
   * State0 ==
   *    __temporal_t_1 = FALSE
   * /\ __temporal_t_1_unroll = FALSE
   * }}}
   *
   * Here, the NameReplacementMap used was
   * {{{
   *  "__temporal_t_1" -> "♢(x = 11)",
   *  "__temporal_t_1_unroll" -> "♢(x = 11)_unroll"
   * }}}
   *
   * Here, the nameReplacementMap used was
   * {{{
   *  "__temporal_t_1" -> "♢(x = 11)",
   *  "__temporal_t_1_unroll" -> "♢(x = 11)_unroll"
   * }}}
   *
   * Note that the expression and its comment are the same, but the names for {{{__temporal_t_1}}} and
   * {{{__temporal_t_1_unroll}}} were substituted.
   * @see
   *   NameReplacementMap
   */
  def writeWithNameReplacementComment(decl: TlaDecl): Unit = {
    val declDoc = declToDoc(decl) <> line <> line
    if (NameReplacementMap.store.isEmpty) {
      prettyWriteDoc(declDoc)
    } else {
      val declComment = toCommentDoc(decl)
      prettyWriteDoc(declComment <> line <> declDoc)
    }
  }

  // Declarations have a trailing empty line
  def write(decl: TlaDecl): Unit = {
    prettyWriteDoc(declToDoc(decl) <> line <> line)
  }

  def write(expr: TlaEx): Unit = prettyWriteDoc(exToDoc((0, 0), expr, sanitizeID))

  def writeComment(commentStr: String): Unit = {
    prettyWriteDoc(wrapWithComment(commentStr) <> line)
  }

  def writeHeader(moduleName: String, extensionModuleNames: List[String] = List.empty): Unit =
    prettyWriteDoc(
        moduleNameDoc(moduleName) <> moduleExtendsDoc(extensionModuleNames) <> line
    )

  def writeFooter(): Unit = prettyWriteDoc(moduleTerminalDoc)

  private def moduleNameDoc(name: String): Doc = {
    val middle = s" MODULE ${sanitizeID(name)} "
    val nDashes = math.max(5, (layout.textWidth - middle.length) / 2) // int div rounds down
    s"${List.fill(nDashes)("-").mkString}$middle${List.fill(nDashes)("-").mkString}" <> line
  }

  private def moduleExtendsDoc(moduleNames: List[String]): Doc =
    if (moduleNames.isEmpty) emptyDoc
    else line <> text("EXTENDS") <> space <> hsep(moduleNames.map(n => text(sanitizeID(n))), comma) <> line

  private def moduleTerminalDoc: Doc =
    s"${List.fill(layout.textWidth)("=").mkString}" <> line

  def modToDoc(mod: TlaModule, extensionModuleNames: List[String] = List.empty): Doc = {
    moduleNameDoc(mod.name) <>
      moduleExtendsDoc(extensionModuleNames) <>
      lsep((mod.declarations.toList.map(declToDoc(_))) :+ moduleTerminalDoc, line)
  }

  /**
   * Writes the provided expr as a doc. parentPrecedence determines whether and how to wrap expressions with braces.
   * nameResolver substitutes NameExs by the value that results from applying it to the name. If no substitution is
   * wanted, use (x: String) => x.
   */
  def exToDoc(
      parentPrecedence: (Int, Int),
      expr: TlaEx,
      nameResolver: String => String): Doc = {
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
                ssep(top.formalParams.map(toDoc), "," <> softline)

            group("LAMBDA" <> space <> paramsDoc <> text(":") <> space <>
              exToDoc((0, 0), top.body, nameResolver))
        }

      case NameEx(x) =>
        text(nameResolver(x))
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
        exToDoc(op.precedence, e, nameResolver) <> "'"

      case OperEx(TlaSetOper.enumSet) =>
        // an empty set
        text("{}")

      case OperEx(op @ TlaSetOper.enumSet, arg) =>
        // a singleton set
        group("{" <> exToDoc(op.precedence, arg, nameResolver) <> "}")

      case OperEx(op @ TlaSetOper.enumSet, args @ _*) =>
        // a set enumeration, e.g., { 1, 2, 3 }
        val argDocs = args.map(exToDoc(op.precedence, _, nameResolver))
        val commaSeparated = folddoc(argDocs.toList, _ <> text(",") <@> _)
        group(braces(group(softline <> nest(commaSeparated, layout.indent)) <> softline))

      case OperEx(op @ TlaFunOper.tuple, args @ _*) =>
        // a tuple, e.g., <<1, 2, 3>>
        val argDocs = args.map(exToDoc(op.precedence, _, nameResolver))
        val commaSeparated = ssep(argDocs.toList, text(",") <> softline)
        group(text("<<") <> nest(linebreak <> commaSeparated, layout.indent) <> linebreak <> ">>")

      case OperEx(op, args @ _*) if op == TlaBoolOper.and || op == TlaBoolOper.or =>
        // we are not using indented /\ and \/, as they are hard to get automatically
        val sign = if (op == TlaBoolOper.and) "/\\" else "\\/"

        if (args.isEmpty) {
          val const = tla.bool(op == TlaBoolOper.and)
          exToDoc(parentPrecedence, const, nameResolver)
        } else {
          val argDocs = args.map(exToDoc(op.precedence, _, nameResolver)).toList
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
              group(text(sign) <> space <> text(sanitizeID(x.toString)) <> space <>
                text(PrettyWriter.binaryOps(TlaSetOper.in)) <> softline <>
                exToDoc(op.precedence, set, nameResolver) <> text(":")) <>
                nest(line <> exToDoc(op.precedence, pred, nameResolver))
          ) ///

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, x, pred) if op == TlaTempOper.EE || op == TlaTempOper.AA =>
        val sign = PrettyWriter.bindingOps(op)
        val doc =
          group(
              group(text(sign) <> space <> text(x.toString) <> ":") <>
                nest(line <> exToDoc(op.precedence, pred, nameResolver))
          ) ///

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(TlaFunOper.rec, keysAndValues @ _*) =>
        // a record, e.g., [ x |-> 1, y |-> 2 ]
        val (ks, vs) = keysAndValues.zipWithIndex.partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k |-> v
        val boxes =
          keys
            .zip(values)
            .map(p =>
              group(strNoQuotes(p._1) <> space <> "|->" <> nest(line <> exToDoc((0, 0), p._2, nameResolver)))) ///

        group(brackets(nest(ssep(boxes.toList, comma <> line))))

      case OperEx(TlaSetOper.recSet, keysAndValues @ _*) =>
        // a record, e.g., [ x: S, y: T ]
        val (ks, vs) = keysAndValues.zipWithIndex.partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k: v
        val boxes =
          keys
            .zip(values)
            .map(p => group(strNoQuotes(p._1) <> ":" <> nest(line <> exToDoc((0, 0), p._2, nameResolver)))) ///

        group(brackets(nest(ssep(boxes.toList, comma <> line))))

      case OperEx(TlaFunOper.funDef, body, keysAndValues @ _*) =>
        val (ks, vs) = keysAndValues.zipWithIndex.partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k \in v
        val boxes =
          keys
            .zip(values)
            .map(p =>
              group(exToDoc((0, 0), p._1, nameResolver) <> space <> "\\in" <> nest(line <> exToDoc((0, 0), p._2,
                  nameResolver)))) ///

        val binders = ssep(boxes.toList, comma <> line)
        val bodyDoc = exToDoc((0, 0), body, nameResolver)
        group(
            text("[") <>
              nest(line <> binders <> space <> "|->" <> nest(line <> bodyDoc)) <> line <>
              text("]")
        ) ////

      case OperEx(TlaSetOper.map, body, keysAndValues @ _*) =>
        val (ks, vs) = keysAndValues.zipWithIndex.partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k |-> v
        val boxes =
          keys
            .zip(values)
            .map(p =>
              group(exToDoc(TlaSetOper.in.precedence, p._1, nameResolver) <> space <>
                "\\in" <> nest(line <> exToDoc(TlaSetOper.in.precedence, p._2, nameResolver)))) ///

        val binders = ssep(boxes.toList, comma <> line)
        val bodyDoc = exToDoc((0, 0), body, nameResolver)
        group(braces(nest(line <> bodyDoc <> text(":") <> nest(line <> binders)) <> line))

      case OperEx(TlaSetOper.filter, name, set, pred) =>
        val binding = group(
            exToDoc(TlaSetOper.in.precedence, name, nameResolver) <> softline <> "\\in" <>
              nest(line <> exToDoc(TlaSetOper.in.precedence, set, nameResolver))
        ) ///
        // use the precedence (0, 0), as there is no need for parentheses around the predicate
        val filter = exToDoc((0, 0), pred, nameResolver)
        group(
            text("{") <> nest(line <> binding <> ":" <> nest(line <> filter)) <> line <> text("}")
        ) ///

      // a function of multiple arguments that are packed into a tuple: don't print the angular brackets <<...>>
      case OperEx(op @ TlaFunOper.app, funEx, OperEx(TlaFunOper.tuple, args @ _*)) =>
        val argDocs = args.map(exToDoc(op.precedence, _, nameResolver))
        val commaSeparatedArgs = folddoc(argDocs.toList, _ <> text(",") <@> _)
        group(
            exToDoc(TlaFunOper.app.precedence, funEx, nameResolver) <> brackets(commaSeparatedArgs)
        ) ///

      // a function of a single argument
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        group(
            exToDoc(TlaFunOper.app.precedence, funEx, nameResolver) <>
              text("[") <> nest(linebreak <> exToDoc(TlaFunOper.app.precedence, argEx,
                  nameResolver)) <> linebreak <> text("]")
        ) ///

      case OperEx(TlaControlOper.ifThenElse, pred, thenEx, elseEx) =>
        val prec = TlaControlOper.ifThenElse.precedence
        val doc =
          group(
              text("IF") <> space <> exToDoc(prec, pred, nameResolver) <> line <>
                text("THEN") <> space <> exToDoc(prec, thenEx, nameResolver) <> line <>
                text("ELSE") <> space <> exToDoc(prec, elseEx, nameResolver)
          ) ///

        wrapWithParen(parentPrecedence, prec, doc)

      case OperEx(TlaControlOper.caseWithOther, otherEx, guardsAndUpdates @ _*) =>
        val prec = TlaControlOper.caseWithOther.precedence
        val (gs, us) = guardsAndUpdates.zipWithIndex.partition(_._2 % 2 == 0)
        val (guards, updates) = (gs.map(_._1), us.map(_._1))
        // format each guard-update pair (g, u) into ![g] = u
        val pairs =
          guards
            .zip(updates)
            .map(p =>
              group(exToDoc(prec, p._1, nameResolver) <>
                nest(line <> text("->") <> space <> exToDoc(prec, p._2, nameResolver)))) ///

        val pairsWithOther =
          if (otherEx == NullEx) {
            pairs
          } else {
            pairs :+ group("OTHER" <> nest(line <> "->" <> space <> exToDoc(prec, otherEx, nameResolver)))
          }

        val doc = group(text("CASE") <> nest(space <> folddoc(pairsWithOther.toList, _ <> line <> "[]" <> space <> _)))
        wrapWithParen(parentPrecedence, prec, doc)

      case opex @ OperEx(TlaControlOper.caseNoOther, guardsAndUpdates @ _*) =>
        // delegate this case to CASE with OTHER by passing NullEx
        exToDoc(parentPrecedence, OperEx(TlaControlOper.caseWithOther, NullEx +: guardsAndUpdates: _*)(opex.typeTag),
            nameResolver)

      case OperEx(TlaFunOper.except, funEx, keysAndValues @ _*) =>
        val (ks, vs) = TlaOper.deinterleave(keysAndValues)

        val indexDocs = ks.collect {
          case OperEx(TlaFunOper.tuple, indices @ _*) =>
            val docs = indices.map(exToDoc((0, 0), _, nameResolver))
            ssep(docs.toList, text(",") <> softline)

          case _ =>
            throw new MalformedTlaError("Malformed expression", expr)
        }

        val valueDocs = vs.map(v => exToDoc((0, 0), v, nameResolver))

        // format each key-value pair (k, v) into ![k] = v
        val boxes =
          indexDocs
            .zip(valueDocs)
            .map { case (index, value) =>
              group(text("!") <> brackets(index) <> space <> text("=") <>
                nest(line <> value))
            } ///

        val updates = ssep(boxes.toList, comma <> line)

        val doc =
          text("[") <> nest(line <> exToDoc(TlaFunOper.except.precedence, funEx, nameResolver) <>
            nest(softline <> text("EXCEPT") <> line <> updates)) <> line <>
            text("]")

        group(doc)

      // a set of functions [S -> T]
      case OperEx(TlaSetOper.funSet, domain, coDomain) =>
        val doc =
          exToDoc(TlaSetOper.funSet.precedence, domain, nameResolver) <>
            nest(line <>
              text("->") <> space <>
              exToDoc(TlaSetOper.funSet.precedence, coDomain, nameResolver))
        group(brackets(doc))

      // a labelled expression L3(a, b) :: 42
      case expr @ OperEx(oper @ TlaOper.label, decoratedExpr, ValEx(TlaStr(name)), args @ _*) =>
        val argDocs = args.map {
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
            nest(line <> exToDoc(oper.precedence, decoratedExpr, nameResolver))
        group(wrapWithParen(parentPrecedence, oper.precedence, doc))

      // [A]_vars or <A>_vars
      case OperEx(op, action, vars) if op == TlaActionOper.stutter || op == TlaActionOper.nostutter =>
        def wrapper = if (op == TlaActionOper.stutter) brackets _ else angles _

        val doc =
          wrapper(exToDoc(op.precedence, action, nameResolver)) <>
            "_" <> exToDoc(op.precedence, vars, nameResolver)
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      case OperEx(op, vars, action) if op == TlaTempOper.weakFairness || op == TlaTempOper.strongFairness =>
        val sign = if (op == TlaTempOper.weakFairness) "WF" else "SF"
        val doc =
          sign <> "_" <> exToDoc(op.precedence, vars, nameResolver) <>
            parens(exToDoc(op.precedence, action, nameResolver))
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      case OperEx(op, arg @ NameEx(_)) if PrettyWriter.unaryOps.contains(op) =>
        val doc = text(PrettyWriter.unaryOps(op)) <> exToDoc(op.precedence, arg, nameResolver)
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, arg @ ValEx(_)) if PrettyWriter.unaryOps.contains(op) =>
        val doc = text(PrettyWriter.unaryOps(op)) <> exToDoc(op.precedence, arg, nameResolver)
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, arg @ OperEx(_, _)) if PrettyWriter.unaryOps.contains(op) =>
        // a unary operator over unary operator, no parentheses needed
        val doc = text(PrettyWriter.unaryOps(op)) <> exToDoc(op.precedence, arg, nameResolver)
        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(TlaFunOper.recFunRef) =>
        text(recFunName) // even if the name is undefined, print it

      // a unary operator that is mapped to Apalache IR
      case OperEx(op, arg) if PrettyWriter.unaryOps.contains(op) =>
        // in all other cases, introduce parentheses.
        // Yse the minimal precedence, as we are introducing the parentheses in any case.
        text(PrettyWriter.unaryOps(op)) <> parens(exToDoc((0, 0), arg, nameResolver))

      // a binary infix operator that is mapped to Apalache IR
      case OperEx(op, lhs, rhs) if PrettyWriter.binaryOps.contains(op) =>
        val doc =
          exToDoc(op.precedence, lhs, nameResolver) <>
            nest(line <>
              text(PrettyWriter.binaryOps(op)) <> space <>
              exToDoc(op.precedence, rhs, nameResolver))
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      // a user-defined binary infix operator such as :> or @@
      case OperEx(TlaOper.apply, NameEx(operName), lhs, rhs) if PrettyWriter.userDefinedBinaryOps.contains(operName) =>
        val doc =
          exToDoc((0, 0), lhs, nameResolver) <>
            nest(line <>
              text(operName) <> space <>
              exToDoc((0, 0), rhs, nameResolver))
        wrapWithParen(parentPrecedence, (0, 0), group(doc))

      // a n-ary operator that is mapped to Apalache IR
      case OperEx(op, args @ _*) if PrettyWriter.naryOps.contains(op) =>
        val sign = PrettyWriter.naryOps(op)
        val argDocs = args.map(exToDoc(op.precedence, _, nameResolver)).toList
        val doc = nest(folddoc(argDocs, _ <> line <> sign <> space <> _))
        wrapWithParen(parentPrecedence, op.precedence, group(doc))

      case OperEx(op @ TlaOper.apply, NameEx(name), args @ _*) =>
        // apply an operator by its name, e.g., F(x)
        val argDocs = args.map(exToDoc(op.precedence, _, nameResolver)).toList
        val commaSeparated = ssep(argDocs, "," <> softline)
        val doc =
          if (args.isEmpty) {
            text(parseableName(name))
          } else {
            group(parseableName(name) <> parens(commaSeparated))
          }

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op @ TlaOper.apply, operEx, args @ _*) =>
        // apply an operator by its definition, e.g., (LAMBDA x: x)(y)
        val argDocs = args.map(exToDoc(op.precedence, _, nameResolver)).toList
        val commaSeparated = ssep(argDocs, "," <> softline)
        val doc = group(parens(exToDoc((0, 0), operEx, nameResolver)) <> parens(commaSeparated))

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case OperEx(op, args @ _*) =>
        val argDocs = args.map(exToDoc(op.precedence, _, nameResolver)).toList
        val commaSeparated = ssep(argDocs, "," <> softline)
        // The standard operators may contain a '!' that refers to the standard module. Remove it.
        val lastIndexOfBang = op.name.lastIndexOf("!")
        val unqualifiedName = if (lastIndexOfBang < 0) op.name else (op.name.substring(lastIndexOfBang + 1))
        val doc =
          if (args.isEmpty) {
            text(unqualifiedName)
          } else {
            group(unqualifiedName <> parens(commaSeparated))
          }

        wrapWithParen(parentPrecedence, op.precedence, doc)

      case LetInEx(body, d @ TlaOperDecl("LAMBDA", _, _)) =>
        // save the declaration and unpack it later, when NameEx(LAMBDA) is met
        lambdaStack = d :: lambdaStack // push the lambda definition on the top
        val doc = exToDoc((0, 0), body, nameResolver)
        lambdaStack = lambdaStack.tail // pop the lambda definition
        doc

      case LetInEx(body, decls @ _*) =>
        def eachDecl(d: TlaOperDecl) = {
          group("LET" <> space <> declToDoc(d) <> line <> "IN")
        }

        group(ssep(decls.map(eachDecl).toList, line) <>
          line <> exToDoc((0, 0), body, nameResolver))

      case expr => throw new PrettyPrinterError(s"PrettyPrinter failed toDoc conversion on expression ${expr}")
    }
  }

  /**
   * Pretty-writes the given decl, while replacing names with the values in the NameReplacementMap. Then, wrap the
   * result as a comment, since the substituted names might not be valid TLA.
   */
  def toCommentDoc(decl: TlaDecl): Doc = {
    wrapWithComment(declToDoc(decl,
            nameResolver = (x: String) => {
              NameReplacementMap.store.getOrElse(x, x)
            }))
  }

  def declToDoc(decl: TlaDecl, nameResolver: String => String = sanitizeID): Doc = {
    val annotations = declAnnotator(layout)(decl)

    decl match {
      case TlaConstDecl(name) =>
        if (annotations.isEmpty) {
          group("CONSTANT" <> space <> parseableName(name))
        } else {
          "CONSTANT" <> nest(line <> wrapWithComment(annotations.get) <> line <> parseableName(name))
        }

      case TlaVarDecl(name) =>
        if (annotations.isEmpty) {
          group("VARIABLE" <> space <> parseableName(name))
        } else {
          "VARIABLE" <> nest(line <> wrapWithComment(annotations.get) <> line <> parseableName(name))
        }

      case TlaAssumeDecl(definedName, body) =>
        val doc = definedName match {
          case None       => group("ASSUME" <> parens(exToDoc((0, 0), body, nameResolver)))
          case Some(name) => group("ASSUME" <+> name <+> "==" <+> parens(exToDoc((0, 0), body, nameResolver)))
        }

        if (annotations.isEmpty) {
          doc
        } else {
          // there is no use case for annotations of assume, but we nevertheless implement it
          wrapWithComment(annotations.get) <> line <> doc
        }

      // a declaration of a recursive function
      case TlaOperDecl(name, List(), OperEx(TlaFunOper.recFunDef, body, keysAndValues @ _*)) =>
        val (ks, vs) = keysAndValues.zipWithIndex.partition(_._2 % 2 == 0)
        val (keys, values) = (ks.map(_._1), vs.map(_._1))
        // format each key-value pair (k, v) into k \in v
        val boxes =
          keys
            .zip(values)
            .map(p =>
              group(
                  exToDoc((0, 0), p._1, nameResolver)
                    <> space
                    <> "\\in"
                    <> nest(line <> exToDoc((0, 0), p._2, nameResolver))
              )) ///

        val binders = ssep(boxes.toList, comma <> line)

        // set the name of the recursive function. TLA+ forbids mutual recursion, so we do not need a stack
        recFunName = name
        // [x \in S]
        val binding = brackets(binders)
        // f[x \in S] == e
        val doc =
          parseableName(name) <> binding <> space <> "==" <> space <> exToDoc((0, 0), body, nameResolver)
        recFunName = REC_FUN_UNDEFINED
        if (annotations.isEmpty) {
          group(doc)
        } else {
          wrapWithComment(annotations.get) <> line <> group(doc)
        }

      // an operator declaration (may be recursive)
      case tod @ TlaOperDecl(name, params, body) =>
        val recPreambule =
          if (!tod.isRecursive) {
            None
          } else {
            Some("RECURSIVE" <> space <> toDoc(OperParam(parseableName(name), params.length)))
          }

        val paramsDoc =
          if (params.isEmpty) {
            text("")
          } else {
            parens(ssep(params.map(toDoc), "," <> softline))
          }

        val declDoc =
          group(parseableName(name) <> paramsDoc <> space <> "==" <> nest(line <> exToDoc((0, 0), body, nameResolver)))
        if (annotations.isEmpty) {
          recPreambule.map(_ <> line <> declDoc).getOrElse(declDoc)
        } else {
          val withComment = wrapWithComment(annotations.get) <> line <> declDoc
          recPreambule.map(_ <> line <> withComment).getOrElse(withComment)
        }
    }
  }

  private def toDoc(param: OperParam): Doc = {
    if (param.isOperator) {
      group(parseableName(param.name) <> parens(ssep(List.fill(param.arity)("_"), "," <> softline)))
    } else {
      parseableName(param.name)
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

  private def wrapWithComment(comment: Doc): Doc = {
    text("(*") <> space <> comment <> space <> text("*)")
  }

  private def wrapWithComment(strings: List[String]): Doc = {
    text("(*") <> nest(lsep(strings.map(text), ""), defaultIndent) <> line <> text("*)")
  }

  private def strNoQuotes(ex: TlaEx): String = {
    ex match {
      case ValEx(TlaStr(s)) => s
      case _                => throw new IllegalStateException("Expected a string as a record key, found: " + ex)
    }
  }

  // A precompiled regex of patterns that are invalid in a TLA identifier
  // Matches:
  //
  // - `::`, Used by apalache for "namespacing" and module imports
  // - Anything that is not a TLA+2 "NameChar".
  //   See https://github.com/tlaplus/tlaplus-standard/blob/main/grammar/TLAPlus2Grammar.tla#L26
  //
  // We treat `::` special so that it will be replaced with a single `_`
  private val invalidIdentifierParts = """(::|[^a-zA-Z0-9_])""".r

  // In our tests, TLC will only accept identifiers that start with a prefix
  // matching this pattern, even tho the spec of the grammar says numerals should
  // also be valid following an underscore.
  // See https://github.com/tlaplus/tlaplus-standard/blob/main/grammar/TLAPlus2Grammar.tla#L26
  private val validIdentifierPrefix = """_*[a-zA-Z]""".r

  // Sanitize an identifier to ensure it can be read by TLC
  private def sanitizeID(s: String): String = {
    val s0 = if (validIdentifierPrefix.findPrefixOf(s).isDefined) s else "id" + s
    invalidIdentifierParts.replaceAllIn(s0, "_")
  }

  private def parseableName(name: String): String = {
    // An operator name may contain '!' if it comes from an instance. Replace '!' with "_i_".
    // Additionally, the name may contain '$', which is produced during preprocessing. Replace '$' with "_si_".
    sanitizeID(name.replaceAll("!", "_i_").replaceAll("\\$", "_si_"))
  }

  def close(): Unit = writer.close()
}

object PrettyWriter {

  /**
   * Write a module to a file (without appending).
   *
   * @param module
   *   a TLA module
   * @param outputFile
   *   an output file that will be created or overwritten
   */
  def write(module: TlaModule, outputFile: File): Unit = {
    val writer = new PrintWriter(new FileWriter(outputFile, false))
    try {
      new PrettyWriter(writer).write(module)
    } finally {
      writer.close()
    }
  }

  def writeAsString(module: TlaModule, extendedModules: List[String] = TlaWriter.STANDARD_MODULES): String = {
    val buf = new StringWriter()
    val prettyWriter = new PrettyWriter(new PrintWriter(buf))
    prettyWriter.write(module, extendedModules)
    buf.toString()
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
      TlaTempOper.diamond -> "<>",
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
        TlaArithOper.div -> "\\div",
        TlaArithOper.mod -> "%",
        TlaArithOper.realDiv -> "/",
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
        ApalacheOper.assign -> ":=",
    ) ////

  // binary operators that are not mapped to Apalache operators
  protected val userDefinedBinaryOps =
    HashSet(":>", "@@")

  protected val naryOps: Map[TlaOper, String] = HashMap(
      TlaSetOper.times -> "\\X"
  ) ////

  protected val bindingOps = HashMap(
      TlaBoolOper.exists -> "\\E",
      TlaBoolOper.forall -> "\\A",
      TlaOper.chooseBounded -> "CHOOSE",
      TlaTempOper.EE -> "\\EE",
      TlaTempOper.AA -> "\\AA",
  ) ////
}
