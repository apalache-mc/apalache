package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import tla2sany.semantic._

/**
  * Translate operator applications. As many TLA+ happen to be operators, this class will be complex...
  *
  * @author konnov
  */
class OpApplTranslator(context: Context) {
  def translate(node: OpApplNode): TlaEx = {
    if (node.getArgs.length == 0) {
      if (node.getOperator.getKind == ASTConstants.BuiltInKind) {
        // that must be a built-in constant operator
        translateBuiltinConst(node)
      } else {
        // this must be a reference to a constant (not a literal!), a variable, or another operator
        translateConstOper(node)
      }
    } else {
      // non-constant operators
      if (node.getOperator.getKind == ASTConstants.BuiltInKind) {
        translateBuiltin(node)
      } else {
        throw new SanyImporterException("Unsupported operator type: " + node.getOperator)
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // a built-in operator with zero arguments, that is, a built-in constant
  private def translateBuiltinConst(node: OpApplNode) = {
    // comparing the name seems to be the only way of learning about the actual operator
    node.getOperator.getName.toString match {
      case "FALSE" => ValEx(TlaFalse) // here we disagree with tlatools and treat FALSE as a built-in value
      case "TRUE" => ValEx(TlaTrue) // ditto
      case _ => throw new SanyImporterException("Unsupported constant built-in operator: " + node.getOperator)
    }
  }

  // a constant operator, that is, a variable or a constant
  private def translateConstOper(node: OpApplNode) = {
    val oper = node.getOperator
    oper.getKind match {
      case ASTConstants.ConstantDeclKind =>
        NameEx(oper.getName.toString.intern())

      case ASTConstants.VariableDeclKind =>
        NameEx(oper.getName.toString.intern())

      case ASTConstants.UserDefinedOpKind =>
        context.declarationsMap.get(oper.getName.toString) match {
          case Some(d: TlaOperDecl) =>
            OperEx(d.operator)

          case _ =>
            throw new SanyImporterException("User-defined operator %s not found".format(oper.getName.toString))
        }
    }
  }

  // a non-constant built-in operator
  private def translateBuiltin(node: OpApplNode) = {
    val opcode = node.getOperator.getName.toString
    OpApplTranslator.simpleOpcodeToTlaOper.get(opcode) match {
      case Some(op) => // the simple translation rule applies
        // if the arities do not match, there must be a problem:
        // either in the definition of the IR operator, or in the map opcodeToIrOp
        assert(op.isCorrectArity(node.getArgs.length))
        val exTran = new ExprOrOpArgNodeTranslator(context)
        val args = node.getArgs.toList.map (exTran.translate)
        OperEx(op, args: _*)

      case None => // a more complicated translation rule is needed
        opcode match {
          case "$BoundedChoose" | "$BoundedExists" | "$BoundedForall" =>
            val exTran = new ExprOrOpArgNodeTranslator(context)
            val args = node.getArgs.toList.map (exTran.translate)
            mkQuantifiedBuiltin(node, opcode, args)

          case "$Case" =>
            // we cannot translate the arguments right here, as in case of OTHER, the guard is just null.
            mkCaseBuiltin(node)

          case "$Except" =>
            mkExceptBuiltin(node)

          case _ =>
            throw new SanyImporterException("Unsupported operator: " + opcode)
        }
    }
  }

  // construct an operator for an expression that introduces a variable
  private def mkQuantifiedBuiltin(node: OpApplNode, opcode: String, args: Seq[TlaEx]): TlaEx = {
    assert(args.length == 1)
    val (pred: TlaEx) = args.head

    /**
      * The following comment is copied verbatim from tla2sany.semantic.OpApplNode:
      *
      * For the OpApplNode representing \E u \in V,  x, y \in S,  <<z, w>> \in R  :  P
      *
      *  - getBdedQuantSymbolLists returns the array of arrays of nodes [ [u], [x, y], [z, w] ]
      *  - isBdedQuantATuple() returns the array of booleans [ false, false, true ]
      *  - getBdedQuantBounds() returns the array of nodes [ V, S, R ]
      */

    // In contrast to TLA tools, we unfold quantified expressions,
    // that is, the example above will be translated into:
    //
    //   \E u \in V: \E x \in S: \E y \in S: \E <<z, w>> \in R : P
    sealed abstract class QExp

    case class QVar(param: FormalParamNode, bound: ExprNode) extends QExp

    case class QTuple(params: List[FormalParamNode], bound: ExprNode) extends QExp

    val paramsAndBounds = node.getBdedQuantSymbolLists.toList.zip(node.getBdedQuantBounds)
    val paramsAndBoundsAndTuples = paramsAndBounds.zip(node.isBdedQuantATuple)
    // construct a list of lists, each containing either a QTuple, or a QVar
    val qexpListList = paramsAndBoundsAndTuples.map {
      case ((params: Array[FormalParamNode], bound: ExprNode), true) =>
        // it's a tuple like <<x, y>> \in S
        List(QTuple(params.toList, bound))

      case ((params: Array[FormalParamNode], bound: ExprNode), false) =>
        // it's an expression like x, y \in S
        params.toList.map {
          p => QVar(p, bound)
        }
    }
    // flatten the list
    val qexps = List.concat(qexpListList: _*)
    // recursively construct a chain of expressions, e.g., \E x \in S: (\E y \in S: P)
    val oper = OpApplTranslator.quantOpcodeToTlaOper(opcode)
    val expTrans = new ExprOrOpArgNodeTranslator(context)

    def toExpr(xs: List[QExp]): TlaEx =
      xs match {
        case Nil =>
          pred

        case QVar(param, bound) :: es =>
          val nested = toExpr(es)
          OperEx(oper, NameEx(param.getName.toString), expTrans.translate(bound), nested)

        case QTuple(params, bound) :: es =>
          val nested = toExpr(es)
          val names = params map {
            p => NameEx(p.getName.toString)
          }
          // construct a tuple expression
          val tuple = OperEx(TlaFunOper.tuple, names: _*)
          // and then a quantifer over this tuple expression
          OperEx(oper, tuple, expTrans.translate(bound), nested)
      }

    toExpr(qexps)
  }

  private def unpackPairs(exTran: ExprOrOpArgNodeTranslator)(pairNodes: List[ExprOrOpArgNode]) = {
    pairNodes.map {
      case arg: OpApplNode =>
        assert("$Pair" == arg.getOperator.getName.toString)
        val pair = arg.getArgs
        assert(2 == pair.length)
        (exTran.translate(pair.head), exTran.translate(pair.tail.head))

      case e =>
        throw new SanyImporterException("Expected a pair, found: " + e)
    }.foldLeft(List[TlaEx]()) {
      case (lst, (g, e)) => e :: g :: lst
    }.reverse
  }

  private def mkCaseBuiltin(node: OpApplNode): TlaEx = {
    val exTran = new ExprOrOpArgNodeTranslator(context)
    val (others, options) = node.getArgs.toList.partition {
      case n: OpApplNode => n.getArgs.head == null
      case _ => false
    }
    assert(others.length <= 1) // what use are several OTHERs?

    val interleaved = unpackPairs(exTran)(options)

    if (others.isEmpty) {
      OperEx(TlaControlOper.caseNoOther, interleaved: _*)
    } else {
      val other = exTran.translate(others.head.asInstanceOf[OpApplNode].getArgs.apply(1))
      OperEx(TlaControlOper.caseWithOther, other +: interleaved: _*)
    }
  }

  private def mkExceptBuiltin(node: OpApplNode): TlaEx = {
    val exTran = new ExprOrOpArgNodeTranslator(context)
    node.getArgs.toList match {
      case (fnode: OpApplNode) :: pairNodes =>
        val fun = exTran.translate(fnode)
        // Note that -- as in TLA tools -- the updated indices are represented with sequences (i.e., tuples),
        // in order to support multidimensional arrays
        OperEx(TlaFunOper.except, fun +: unpackPairs(exTran)(pairNodes): _*)

      case _ =>
        throw new SanyImporterException("Unexpected structure of EXCEPT")
    }
  }
}

object OpApplTranslator {
  /**
    * A mapping from the Tlatools operator code to our IR operators.
    * This simple mapping does not apply to CHOOSE, \E, and \A.
    */
  val simpleOpcodeToTlaOper: Map[String, TlaOper] = Map(
    ("=", TlaOper.eq),
    ("/=", TlaOper.ne),
    ("'", TlaActionOper.prime),
    ("\\lnot", TlaBoolOper.not),
    ("\\lor", TlaBoolOper.or),
    ("\\land", TlaBoolOper.and),
    ("\\equiv", TlaBoolOper.equiv),
    ("=>", TlaBoolOper.implies),
    ("SUBSET", TlaSetOper.powerset),
    ("UNION", TlaSetOper.union),
    ("DOMAIN", TlaFunOper.domain),
    ("\\subseteq", TlaSetOper.subseteq),
    ("\\in", TlaSetOper.in),
    ("\\notin", TlaSetOper.notin),
    ("\\", TlaSetOper.setminus),
    ("\\intersect", TlaSetOper.cap),
    ("\\union", TlaSetOper.cup),
    ("$CartesianProd", TlaSetOper.times),
    ("~>", TlaTempOper.leadsTo),
    ("[]", TlaTempOper.box),
    ("<>", TlaTempOper.diamond),
    ("ENABLED", TlaActionOper.enabled),
    ("UNCHANGED", TlaActionOper.unchanged),
    ("\\cdot", TlaActionOper.composition),
    ("-+->", TlaTempOper.guarantees),
    ("$AngleAct", TlaActionOper.nostutter),
    ("$Tuple", TlaFunOper.tuple),
    ("$Pair", TlaFunOper.tuple),
    ("$ConjList", TlaBoolOper.and),
    ("$DisjList", TlaBoolOper.or),
    ("$Seq", TlaFunOper.tuple)
  )
  // A mapping from the opcodes of quantified operators (\E, \A, CHOOSE) to our IR operators.
  val quantOpcodeToTlaOper: Map[String, TlaOper] = Map(
    ("$BoundedChoose", TlaOper.chooseBounded),
    ("$BoundedExists", TlaBoolOper.exists),
    ("$BoundedForall", TlaBoolOper.forall)
  )
  // A mapping for other operators
  val otherOpcodeToTlaOper: Map[String, TlaOper] = Map(
    ("$Case", TlaControlOper.caseNoOther)
  )
}