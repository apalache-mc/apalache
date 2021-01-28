package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaStrSet}
import at.forsyte.apalache.tla.lir.values.TlaBool
import tla2sany.semantic._

/**
  * Translate operator applications. As many TLA+ expressions are defined via operators, this class is quite complex.
  *
  * @author konnov
  */
class OpApplTranslator(
    sourceStore: SourceStore,
    annotationStore: AnnotationStore,
    val context: Context,
    val recStatus: RecursionStatus
) {

  // we use the following case classes to represent the bound variables with a range in many quantified expressions
  private sealed abstract class BExp

  private case class BVar(param: FormalParamNode, bound: ExprNode) extends BExp

  private case class BTuple(params: List[FormalParamNode], bound: ExprNode)
      extends BExp

  // we use the following case classes to represent the bound variables without range in many quantified expressions
  private sealed abstract class UExp

  private case class UVar(param: FormalParamNode) extends UExp

  private case class UTuple(params: List[FormalParamNode]) extends UExp

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
      val oper = node.getOperator
      // non-constant operators
      oper.getKind match {
        // an operator that is at the core of TLA+, e.g., { 1 }, \A x \in S: e
        case ASTConstants.BuiltInKind =>
          translateBuiltin(node)

        // an operator parameter that must be an operator itself
        case ASTConstants.FormalParamKind =>
          translateFormalParam(node)

        // either a user-defined operator or an operator from the standard library, e.g., Sequences
        case ASTConstants.UserDefinedOpKind =>
          translateUserOperator(node)

        case _ =>
          throw new SanyImporterException(
            "Unsupported operator type: " + node.getOperator
          )
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // call to a user-defined operator (may come from the standard library), either a LOCAL one, or not
  private def translateUserOperator(applyNode: OpApplNode) = {
    if (!applyNode.getOperator.isLocal) {
      translateNonLocalUserOperator(applyNode)
    } else {
      // issue 295: https://github.com/informalsystems/apalache/issues/295
      // LOCAL operators may originate from the standard library :face_palm
      // For instance, if the user writes LOCAL INSTANCE Sequences
      applyNode.getOperator match {
        case opdef: OpDefNode =>
          // translate as an application of a standard library operator
          translateLocalLibraryOperatorOrValue(opdef, applyNode)
            .getOrElse {
              // or as an application of a local user-defined operator
              translateLocalOperator(opdef, applyNode)
            }

        case _ =>
          val msg = "Expected a LOCAL operator defined with OpDefNode, found: " + applyNode.getOperator.getClass
          throw new SanyImporterException(msg)
      }
    }
  }

  // call an operator or a value (e.g., Sequences!Append or Integers!Int) from a standard module
  // that is instantiated with LOCAL INSTANCE
  private def translateLocalLibraryOperatorOrValue(
      opdef: OpDefNode,
      applyNode: OpApplNode
  ): Option[TlaEx] = {
    val source = opdef.getSource
    if (source == null || source.getOriginallyDefinedInModuleNode == null) {
      None
    } else {
      val operatorName = source.getName.toString
      // the original module, in which the operator is defined
      val modName = source.getOriginallyDefinedInModuleNode.getName.toString
      StandardLibrary.libraryOperators
        .get((modName, operatorName))
        .map {
          // a library operator
          tlaOper =>
            val exTran =
              ExprOrOpArgNodeTranslator(
                sourceStore,
                annotationStore,
                context,
                recStatus
              )
            val args = applyNode.getArgs.toList.map { p =>
              exTran.translate(p)
            }
            OperEx(tlaOper, args: _*)
        }
        .orElse {
          // a library value
          StandardLibrary.libraryValues.get((modName, operatorName)).map(ValEx)
        }
    }
  }

  // call a user-defined operator that is defined locally
  private def translateLocalOperator(
      opdef: OpDefNode,
      node: OpApplNode
  ): TlaEx = {
    // Since we do not know the original location of the local operator,
    // we can only re-define it with a LET-IN expression
    // translate the declaration of the LOCAL operator
    val decl =
      OpDefTranslator(sourceStore, annotationStore, context).translate(opdef)
    // translate its arguments
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )
    val args = node.getArgs.toList.map { p =>
      exTran.translate(p)
    }
    val refByName = NameEx(decl.name)
    sourceStore.add(refByName.ID, SourceLocation(node.getLocation)) // record the source location
    // apply the operator by its name
    val app = OperEx(TlaOper.apply, refByName +: args: _*)
    sourceStore.add(app.ID, SourceLocation(node.getLocation)) // record the source location
    // return the expression LET F(..) = .. IN F(args)
    LetInEx(app, decl)
  }

  // call a user-defined operator that is not defined with LOCAL
  private def translateNonLocalUserOperator(node: OpApplNode) = {
    val opcode = node.getOperator.getName.toString
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )

    def translateNonRec(): TlaEx = {
      context.lookup(opcode) match {
        case DeclUnit(decl: TlaOperDecl) =>
          // call the user-defined operator
          val args = node.getArgs.toList.map { p =>
            exTran.translate(p)
          }
          OperEx(TlaOper.apply, NameEx(decl.name) +: args: _*)

        case NoneUnit() =>
          // call the user-defined operator that is under construction
          val args = node.getArgs.toList.map { p =>
            exTran.translate(p)
          }
          OperEx(TlaOper.apply, NameEx(opcode) +: args: _*)

        case OperAliasUnit(_, oper) =>
          // call the library operator that is bound to the alias, e.g., instead of I!+ call +.
          val args = node.getArgs.toList.map { p =>
            exTran.translate(p)
          }
          OperEx(oper, args: _*)

        case ValueAliasUnit(_, value) =>
          // just use the TLA+ value
          ValEx(value)

        case _ =>
          throw new SanyImporterException(
            "User operator %s is not found in the translation context: %s"
              .format(opcode, node)
          )
      }
    }

    if (recStatus == InsideRecursion()) {
      node.getOperator match {
        case oper: OpDefNode if oper.getInRecursive =>
          // this is a placeholder for a recursive call, replace it with a usage of a formal parameter
          val args = node.getArgs.toList.map { p =>
            exTran.translate(p)
          }
          val recParam = OperFormalParam(opcode, args.length)
          OperEx(TlaOper.apply, NameEx(opcode) +: args: _*)

        case _ =>
          translateNonRec()
      }
    } else {
      translateNonRec()
    }
  }

  // translate an operator application that uses a parameter operator, i.e.,
  // in A(B(_)) == B(1), translate the application B(1)
  private def translateFormalParam(node: OpApplNode): TlaEx = {
    val oper = node.getOperator.asInstanceOf[FormalParamNode]
    // FIXME: should we extract the parameter from the context???
    val formalParam =
      FormalParamTranslator().translate(oper).asInstanceOf[OperFormalParam]
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )
    val args = node.getArgs.toList.map { p =>
      exTran.translate(p)
    }
    OperEx(TlaOper.apply, NameEx(formalParam.name) +: args: _*)
  }

  // a built-in operator with zero arguments, that is, a built-in constant
  private def translateBuiltinConst(node: OpApplNode) = {
    // comparing the name seems to be the only reasonable way of learning about the actual operator
    node.getOperator.getName.toString match {
      case "FALSE"         => ValEx(TlaBool(false))
      case "TRUE"          => ValEx(TlaBool(true))
      case "BOOLEAN"       => ValEx(TlaBoolSet)
      case "STRING"        => ValEx(TlaStrSet)
      case "$SetEnumerate" => OperEx(TlaSetOper.enumSet)
      // NOTE: previously, we have a special object for the only empty set is a value,
      // but that seems to create problems
      case "$Tuple" => OperEx(TlaFunOper.tuple) // just an empty tuple/sequence
      case _ =>
        throw new SanyImporterException(
          "Unsupported constant built-in operator: " + node.getOperator
        )
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

      case ASTConstants.FormalParamKind =>
        NameEx(oper.getName.toString.intern())

      case ASTConstants.UserDefinedOpKind =>
        translateUserOperator(node)
    }
  }

  // a non-constant built-in operator
  private def translateBuiltin(node: OpApplNode) = {
    val opcode = node.getOperator.getName.toString
    OpApplTranslator.simpleOpcodeToTlaOper.get(opcode) match {
      case Some(op) => // the simple translation rule applies (the most operators fall in this category)
        // if the arities do not match, there must be a problem:
        // either in the definition of the IR operator, or in the map opcodeToIrOp
        assert(op.isCorrectArity(node.getArgs.length))
        val exTran = ExprOrOpArgNodeTranslator(
          sourceStore,
          annotationStore,
          context,
          recStatus
        )
        val args = node.getArgs.toList.map(exTran.translate)
        OperEx(op, args: _*)

      case None => // a more complicated translation rule is needed
        opcode match {
          case "$BoundedChoose" | "$BoundedExists" | "$BoundedForall" =>
            val exTran =
              ExprOrOpArgNodeTranslator(
                sourceStore,
                annotationStore,
                context,
                recStatus
              )
            val args = node.getArgs.toList.map(exTran.translate)
            mkBoundedQuantifiedBuiltin(node, opcode, args)

          case "$TemporalExists" | "$TemporalForall" | "$UnboundedChoose" |
              "$UnboundedExists" | "$UnboundedForall" =>
            val exTran =
              ExprOrOpArgNodeTranslator(
                sourceStore,
                annotationStore,
                context,
                recStatus
              )
            val args = node.getArgs.toList.map(exTran.translate)
            mkUnboundedQuantifiedBuiltin(node, opcode, args)

          case "$Case" =>
            // we cannot translate the arguments right here, as in case of OTHER, the guard is just null.
            mkCaseBuiltin(node)

          case "$Except" =>
            mkExceptBuiltin(node)

          case "$FcnConstructor" | "$NonRecursiveFcnSpec" =>
            // Note that we always translate a non-recursive function definition as just a function constructor.
            mkBoundCtorBuiltin(TlaFunOper.funDef, node)

          case "$RecursiveFcnSpec" =>
            // A recursive function definition `f[x \in S] == e`
            // is translated into a constructor of a recursive function.
            // Recursive functions are also post-processed by OpDefTranslator.
            mkBoundCtorBuiltin(TlaFunOper.recFunDef, node)

          case "$SetOfAll" =>
            mkBoundCtorBuiltin(TlaSetOper.map, node)

          case "$SubsetOf" =>
            val op =
              mkBoundCtorBuiltin(TlaSetOper.filter, node).asInstanceOf[OperEx]
            // move the predicate to the end, to reflect the natural order { x \in S: p }
            OperEx(TlaSetOper.filter, op.args.tail :+ op.args.head: _*)

          case "$RcdConstructor" =>
            mkPairsCtorBuiltin(TlaFunOper.enum, node)

          case "$SetOfRcds" =>
            mkPairsCtorBuiltin(TlaSetOper.recSet, node)

          case "$Nop" =>
            // typically, an expression related to TLAPS is marked with $Nop
            NullEx // we cannot do much here, but hope that the expression will never reach the model checker

          case _ =>
            throw new SanyImporterException("Unsupported operator: " + opcode)
        }
    }
  }

  private def extractBoundedQuantifiedVariables(
      node: OpApplNode
  ): List[BExp] = {

    /**
      * The following comment is copied verbatim from tla2sany.semantic.OpApplNode:
      *
      * For the OpApplNode representing \E u \in V,  x, y \in S,  <<z, w>> \in R  :  P
      *
      *  - getBdedQuantSymbolLists returns the array of arrays of nodes [ [u], [x, y], [z, w] ]
      *  - isBdedQuantATuple() returns the array of booleans [ false, false, true ]
      *  - getBdedQuantBounds() returns the array of nodes [ V, S, R ]
      */
    val paramsAndBounds =
      node.getBdedQuantSymbolLists.toList.zip(node.getBdedQuantBounds)
    val paramsAndBoundsAndTuples = paramsAndBounds.zip(node.isBdedQuantATuple)
    // construct a list of lists, each containing either a BTuple, or a BVar
    val qexpListList = paramsAndBoundsAndTuples.map {
      case ((params: Array[FormalParamNode], bound: ExprNode), true) =>
        // it's a tuple like <<x, y>> \in S
        List(BTuple(params.toList, bound))

      case ((params: Array[FormalParamNode], bound: ExprNode), false) =>
        // it's an expression like x, y \in S
        params.toList.map { p =>
          BVar(p, bound)
        }
    }
    // flatten the list
    List.concat(qexpListList: _*)
  }

  // construct an operator for an expression that introduces a variable bounded with a range
  private def mkBoundedQuantifiedBuiltin(
      node: OpApplNode,
      opcode: String,
      args: Seq[TlaEx]
  ): TlaEx = {
    assert(args.length == 1)
    val (pred: TlaEx) = args.head
    val qexps = extractBoundedQuantifiedVariables(node)
    // In contrast to TLA tools, we unfold quantified expressions,
    // that is, the expression \E u \in V,  x, y \in S,  <<z, w>> \in R  :  P above will be translated into:
    //
    //   \E u \in V: \E x \in S: \E y \in S: \E <<z, w>> \in R : P

    // recursively construct a chain of expressions, e.g., \E x \in S: (\E y \in S: P)
    val oper = OpApplTranslator.quantOpcodeToTlaOper(opcode)
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )

    def toExpr(xs: List[BExp]): TlaEx =
      xs match {
        case Nil =>
          pred

        case BVar(param, bound) :: es =>
          val nested = toExpr(es)
          OperEx(
            oper,
            NameEx(param.getName.toString),
            exTran.translate(bound),
            nested
          )

        case BTuple(params, bound) :: es =>
          val nested = toExpr(es)
          val names = params map { p =>
            NameEx(p.getName.toString)
          }
          // construct a tuple expression
          val tuple = OperEx(TlaFunOper.tuple, names: _*)
          // and then a quantifer over this tuple expression
          OperEx(oper, tuple, exTran.translate(bound), nested)
      }

    toExpr(qexps)
  }

  private def extractUnboundQuantifiedVariables(
      node: OpApplNode
  ): List[TlaEx] = {

    /**
      * The following comment is copied verbatim from tla2sany.semantic.OpApplNode:
      *
      * These methods identify the OpApplNode's unbounded quantifier
      * symbols. For example, the x, y, and z in
      *
      *     \E x, y, z : P    or   \E <<x, y, z>> : P
      *
      * The method getUnbdedQuantSymbols() returns an array of refs to
      * the FormalParamNodes for x, y, z; and isUnbdedQuantATuple() indicates
      * whether or not there is a << >> around them.
      */
    // why shall we care about a tuple around bounded variables?
    node.getUnbdedQuantSymbols.toList.map { p: FormalParamNode =>
      NameEx(p.getName.toString)
    }
  }

  // construct an operator for an expression that introduces a variable bounded with an unbounded range
  private def mkUnboundedQuantifiedBuiltin(
      node: OpApplNode,
      opcode: String,
      args: Seq[TlaEx]
  ): TlaEx = {
    assert(args.length == 1)
    // In contrast to TLA tools, we unfold quantified expressions,
    // that is, the expression \E u,  x, y,  <<z, w>> :  P above will be translated into:
    //
    //   \E u: \E x: \E y: \E <<z, w>> : P

    // recursively construct a chain of expressions, e.g., \E x: (\E y: P)
    val oper = OpApplTranslator.quantOpcodeToTlaOper(opcode)
    val (pred: TlaEx) = args.head
    extractUnboundQuantifiedVariables(node).foldRight(pred) { (param, e) =>
      OperEx(oper, param, e)
    }
  }

  // translate an expression for a function constructor, e.g., [ x \in X |-> e ] or a set comprehension { e : x \in X }
  private def mkBoundCtorBuiltin(oper: TlaOper, node: OpApplNode): TlaEx = {
    val qexps = extractBoundedQuantifiedVariables(node)
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )
    val body = exTran.translate(node.getArgs.head)
    // e.g., e in the example above
    val boundVars = qexps
      .foldLeft(List[TlaEx]()) { (list, qe) =>
        qe match {
          case BVar(param, bound) =>
            exTran.translate(bound) ::
              NameEx(param.getName.toString) ::
              list

          case BTuple(params, bound) =>
            exTran.translate(bound) ::
              TlaFunOper.mkTuple(params.map { p =>
                NameEx(p.getName.toString)
              }: _*) ::
              list
        }
      }
      .reverse
    OperEx(oper, body +: boundVars: _*)
  }

  // translate a list of pairs into an interleaved list of IR expressions
  private def unpackPairs(
      exTran: ExprOrOpArgNodeTranslator
  )(pairNodes: List[ExprOrOpArgNode]) = {
    pairNodes
      .map {
        case arg: OpApplNode =>
          assert("$Pair" == arg.getOperator.getName.toString)
          val pair = arg.getArgs
          assert(2 == pair.length)
          (exTran.translate(pair.head), exTran.translate(pair.tail.head))

        case e =>
          throw new SanyImporterException("Expected a pair, found: " + e)
      }
      .foldLeft(List[TlaEx]()) {
        case (lst, (g, e)) => e :: g :: lst
      }
      .reverse
  }

  /**
    * Create a constructor that receives a list of pairs:
    *
    * <ul>
    *  <li>a record constructor: [ k_1 |-> v_1, ..., k_n |-> v_ n ], or</li>
    *  <li>a record set constructor: [ k_1 : S_1, ..., k_n: S_n ]</li>
    * </ul>
    */
  private def mkPairsCtorBuiltin(oper: TlaOper, node: OpApplNode): TlaEx = {
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )
    val interleaved = unpackPairs(exTran)(node.getArgs.toList)
    OperEx(oper, interleaved: _*)
  }

  // create a CASE operator
  private def mkCaseBuiltin(node: OpApplNode): TlaEx = {
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )
    val (others, options) = node.getArgs.toList.partition {
      case n: OpApplNode => n.getArgs.head == null
      case _             => false
    }
    assert(others.length <= 1) // what use are several OTHERs?

    val interleaved = unpackPairs(exTran)(options)

    if (others.isEmpty) {
      OperEx(TlaControlOper.caseNoOther, interleaved: _*)
    } else {
      val other =
        exTran.translate(others.head.asInstanceOf[OpApplNode].getArgs.apply(1))
      OperEx(TlaControlOper.caseWithOther, other +: interleaved: _*)
    }
  }

  private def mkExceptBuiltin(node: OpApplNode): TlaEx = {
    val exTran = ExprOrOpArgNodeTranslator(
      sourceStore,
      annotationStore,
      context,
      recStatus
    )
    node.getArgs.toList match {
      case (fnode: ExprNode) :: pairNodes =>
        // For instance, [f EXCEPT ![e1] = e2, ![e3] = e4] or [@ EXCEPT ![e1] = e2, ![e3] = e4]
        // First, translate the expression that encodes the function to be updated.
        val fun = exTran.translate(fnode)
        // Second, translate the expressions that encode the update pairs (e1, e2), (e3, e4), etc.
        // Note that -- as in TLA tools -- the updated indices are represented with sequences (i.e., tuples),
        // in order to support multidimensional arrays.
        OperEx(TlaFunOper.except, fun +: unpackPairs(exTran)(pairNodes): _*)

      case _ =>
        throw new SanyImporterException(
          "Unexpected structure of EXCEPT: " + node
        )
    }
  }
}

object OpApplTranslator {
  def apply(
      sourceSource: SourceStore,
      annotationStore: AnnotationStore,
      context: Context,
      recStatus: RecursionStatus
  ): OpApplTranslator = {
    new OpApplTranslator(sourceSource, annotationStore, context, recStatus)
  }

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
    ("$SquareAct", TlaActionOper.stutter),
    ("$Tuple", TlaFunOper.tuple),
    ("$Pair", TlaFunOper.tuple),
    ("$ConjList", TlaBoolOper.and),
    ("$DisjList", TlaBoolOper.or),
    ("$Seq", TlaFunOper.tuple),
    ("$FcnApply", TlaFunOper.app),
    ("$IfThenElse", TlaControlOper.ifThenElse),
    ("$RcdSelect", TlaFunOper.app),
    ("$SetEnumerate", TlaSetOper.enumSet),
    ("$SetOfFcns", TlaSetOper.funSet),
    ("$SF", TlaTempOper.strongFairness),
    ("$WF", TlaTempOper.weakFairness)
  )
  // A mapping from the opcodes of quantified operators (\E, \A, CHOOSE) to our IR operators.
  val quantOpcodeToTlaOper: Map[String, TlaOper] = Map(
    ("$BoundedChoose", TlaOper.chooseBounded),
    ("$BoundedExists", TlaBoolOper.exists),
    ("$BoundedForall", TlaBoolOper.forall),
    ("$TemporalExists", TlaTempOper.EE),
    ("$TemporalForall", TlaTempOper.AA),
    ("$UnboundedChoose", TlaOper.chooseUnbounded),
    ("$UnboundedExists", TlaBoolOper.existsUnbounded),
    ("$UnboundedForall", TlaBoolOper.forallUnbounded)
  )
  // A mapping for other operators
  val otherOpcodeToTlaOper: Map[String, TlaOper] = Map(
    ("$Case", TlaControlOper.caseNoOther),
    ("$FcnConstructor", TlaFunOper.funDef),
    ("$SetOfAll", TlaSetOper.map),
    ("$SubsetOf", TlaSetOper.filter),
    ("$Except", TlaFunOper.except),
    ("$RcdConstructor", TlaFunOper.enum),
    ("$SetOfRcds", TlaSetOper.recSet)
  )
}
