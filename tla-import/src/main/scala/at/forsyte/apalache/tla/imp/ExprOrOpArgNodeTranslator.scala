package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.control.LetInOper
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.{TlaDecimal, TlaInt, TlaStr}
import tla2sany.semantic._

import scala.collection.JavaConverters._

/**
  * Translate a TLA+ expression.
  *
  * @author konnov
  */
class ExprOrOpArgNodeTranslator(context: Context, recStatus: RecursionStatus) {
  def translate: ExprOrOpArgNode => TlaEx = {
    // as tlatools do not provide us with a visitor pattern, we have to enumerate classes here
    case num: NumeralNode =>
      translateNumeral(num)

    case str: StringNode =>
      translateString(str)

    case dec: DecimalNode =>
      translateDecimal(dec)

    case opApp: OpApplNode =>
      OpApplProxy(OpApplTranslator(context, recStatus)).translate(opApp)

    case arg: OpArgNode =>
      // we just pass the name of the argument without any extra information
      NameEx(arg.getName.toString.intern())

    case letIn: LetInNode =>
      translateLetIn(letIn)

    case at: AtNode =>
      translateAt(at)

    case label: LabelNode =>
      translateLabel(label)

    case n =>
      throw new SanyImporterException("Unexpected subclass of tla2sany.ExprOrOpArgNode: " + n.getClass)
  }

  private def translateNumeral(node: NumeralNode) =
    if (node.bigVal() != null) {
      ValEx(TlaInt(node.bigVal()))
    } else {
      ValEx(TlaInt(node.`val`()))
    }

  private def translateString(str: StringNode) =
  // internalize the string, so several occurences of the same string are kept as the same object
    ValEx(TlaStr(str.getRep.toString.intern()))

  private def translateDecimal(dec: DecimalNode) =
    if (dec.bigVal() != null) {
      ValEx(TlaDecimal(dec.bigVal()))
    } else {
      // the normal math exponent is the negated scale
      ValEx(TlaDecimal(BigDecimal(dec.mantissa(), -dec.exponent())))
    }

  private def translateLetIn(letIn: LetInNode): TlaEx = {
    // Accumulate definitions as in ModuleTranslator.
    // (As ModuleNode does not implement Context, we cannot reuse the code from there.)

    // We only go through the operator definitions, as one cannot define constants or variables with Let-In.
    // For some reason, multiple definitions come in the reverse order in the letIn.context.
    // Hence, we reverse the list first.
    //
    // TODO: properly handle recursive declarations
    val innerContext = letIn.context.getOpDefs.elements.asScala.toList.reverse.foldLeft(Context()) {
      case (ctx, node: OpDefNode) =>
        ctx.push(OpDefTranslator(context.disjointUnion(ctx)).translate(node))

      case (_, other) =>
        throw new SanyImporterException("Expected OpDefNode, found: " + other.getClass)
    }
    val oper = new LetInOper(innerContext.declarations.map {d => d.asInstanceOf[TlaOperDecl]})
    val body = ExprOrOpArgNodeTranslator(context.disjointUnion(innerContext), recStatus).translate(letIn.getBody)
    OperEx(oper, body)
  }

  private def translateAt(node: AtNode): TlaEx = {
    // e.g., in [f EXCEPT ![42] = @ + @], we have: base = f, modifier = 42
    val base = translate(node.getAtBase)
    // This translation introduces new expressions for different occurrences of @.
    // An alternative to this would be to introduce LET at = ... IN [f EXCEPT ![0] = at + at].
    val modifier = translate(node.getAtModifier)
    OperEx(TlaFunOper.app, base, modifier)
  }

  private def translateLabel(node: LabelNode): TlaEx = {
    // There seems to be no way to access the formal parameters of LabelNode.
    // For the moment, just translate the parameters as an empty list
    OperEx(TlaOper.label, translate(node.getBody.asInstanceOf[ExprNode]), NameEx(node.getName.toString))
  }
}

object ExprOrOpArgNodeTranslator {
  def apply(context: Context, recStatus: RecursionStatus): ExprOrOpArgNodeTranslator = {
    new ExprOrOpArgNodeTranslator(context, recStatus)
  }
}
