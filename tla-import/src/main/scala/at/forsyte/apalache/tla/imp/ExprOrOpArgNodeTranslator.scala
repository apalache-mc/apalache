package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.simpl.Desugarer
import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{LetInOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.{TlaDecimal, TlaInt, TlaStr}
import com.typesafe.scalalogging.LazyLogging
import tla2sany.semantic._

import scala.collection.JavaConverters._

/**
  * Translate a TLA+ expression.
  *
  * @author konnov
  */
class ExprOrOpArgNodeTranslator(sourceStore: SourceStore, context: Context, recStatus: RecursionStatus) extends LazyLogging {
  private val desugarer = new Desugarer() // construct elsewhere?

  def translate(node: ExprOrOpArgNode): TlaEx = {
    val result =
      node match {
        // as tlatools do not provide us with a visitor pattern, we have to enumerate classes here
        case num: NumeralNode =>
          translateNumeral(num)

        case str: StringNode =>
          translateString(str)

        case dec: DecimalNode =>
          translateDecimal(dec)

        case opApp: OpApplNode =>
          OpApplProxy(sourceStore, OpApplTranslator(sourceStore, context, recStatus)).translate(opApp)

        case arg: OpArgNode =>
          // we just pass the name of the argument without any extra information
          NameEx(arg.getName.toString.intern())

        case letIn: LetInNode =>
          translateLetIn(letIn)

        case substIn: SubstInNode =>
          translateSubstIn(substIn)

        case at: AtNode =>
          translateAt(at)

        case label: LabelNode =>
          translateLabel(label)

        case n =>
          throw new SanyImporterException("Unexpected subclass of tla2sany.ExprOrOpArgNode: " + n.getClass)
      }

    val sugarFree = desugarer.transform(result)

    sourceStore.addRec(sugarFree, SourceLocation(node.getLocation))
  }

  private def translateNumeral(node: NumeralNode) = {
    if (node.bigVal() != null) {
      ValEx(TlaInt(node.bigVal()))
    } else {
      ValEx(TlaInt(node.`val`()))
    }
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
    var letInDeclarations = List[TlaOperDecl]()
    var letInContext = context
    for (node <- letIn.context.getOpDefs.elements.asScala.toList.reverse) {
      node match {
        case opdef: OpDefNode =>
          val decl = OpDefTranslator(sourceStore, letInContext).translate(opdef)
          letInDeclarations = letInDeclarations :+ decl
          letInContext = letInContext.push(decl)

        case _ =>
          throw new SanyImporterException("Expected OpDefNode, found: " + node)
      }
    }

    val oper = new LetInOper(letInDeclarations)
    val body = ExprOrOpArgNodeTranslator(sourceStore, letInContext, recStatus)
      .translate(letIn.getBody)
    OperEx(oper, body)
  }

  // substitute an expression with the declarations that come from INSTANCE M WITH ...
  private def translateSubstIn(substIn: SubstInNode): TlaEx = {
    SubstTranslator(sourceStore, context)
      .translate(substIn, translate(substIn.getBody))
  }

  private def translateAt(node: AtNode): TlaEx = {
    // e.g., in [f EXCEPT ![42] = @ + @], we have: base = f, modifier = 42
    val base = translate(node.getAtBase)
    // This translation introduces new expressions for different occurrences of @.
    // An alternative to this would be to introduce LET at = ... IN [f EXCEPT ![0] = at + at].

    // BUGFIX: the indices in EXCEPT are packed as tuples.
    // Unpack them into multiple function applications when rewriting @, e.g., (((f[1])[2])[3]).
    translate(node.getAtModifier) match {
      case OperEx(TlaFunOper.tuple, indices@_*) =>
        def applyOne(base: TlaEx, index: TlaEx): TlaEx = {
          OperEx(TlaFunOper.app, base, index)
        }

        indices.foldLeft(base)(applyOne)

      case e@_ =>
        throw new SanyImporterException("Unexpected index expression in EXCEPT: " + e)
    }
  }

  private def translateLabel(node: LabelNode): TlaEx = {
    // There seems to be no way to access the formal parameters of LabelNode.
    // For the moment, just translate the parameters as an empty list
    val labelBody = translate(node.getBody.asInstanceOf[ExprNode])
    OperEx(TlaOper.label, labelBody, ValEx(TlaStr(node.getName.toString)))
  }
}

object ExprOrOpArgNodeTranslator {
  def apply(sourceStore: SourceStore, context: Context, recStatus: RecursionStatus) : ExprOrOpArgNodeTranslator = {
    new ExprOrOpArgNodeTranslator(sourceStore, context, recStatus)
  }
}
