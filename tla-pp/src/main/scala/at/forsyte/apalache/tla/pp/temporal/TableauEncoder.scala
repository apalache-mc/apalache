package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import scalaz.Scalaz.{init => _}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.tla.pp.IrrecoverablePreprocessingError
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import at.forsyte.apalache.tla.pp.temporal.DeclUtils._
import scala.collection.immutable.HashMap
import at.forsyte.apalache.tla.lir.oper.TlaTempOper
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.DeclarationSorter
import at.forsyte.apalache.tla.lir.oper.TlaOper

/**
 * Encodes temporal formulas as invariants.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TableauEncoder(
    module: TlaModule,
    gen: UniqueNameGenerator,
    loopEnc: LoopEncoder,
    tracker: TransformationTracker)
    extends LazyLogging {
  val levelFinder = new TlaLevelFinder(module)
  var varNamesToExStrings = new HashMap[String, String]()

  private def inBoolSet(element: TBuilderInstruction): TBuilderInstruction = builder.in(element, builder.booleanSet())

  /**
   * Encodes each of a sequence of temporal formulas.
   * @see
   *   [[encodeFormula]]
   */
  def temporalsToInvariants(modWithPreds: ModWithPreds, formulas: TlaOperDecl*): TlaModule = {

    val (varDeclSeqs, predsSeq, exVarDecls) = formulas.map(singleTemporalToInvariant).unzip3
    val varDecls = varDeclSeqs.flatten
    val preds = predsSeq.foldLeft(PredExs())(_ ++ _)

    // update init
    val newInit = andInDecl(builder.and(preds.initExs: _*), modWithPreds.init, tracker)

    // update next
    val newNext = andInDecl(builder.and(preds.nextExs: _*), modWithPreds.next, tracker)

    // update loopOK
    val newLoopOK = andInDecl(builder.and(preds.loopOKExs: _*), modWithPreds.loopOK, tracker)
    val loopOKopApp = builder.appOp(builder.name(newLoopOK.name, OperT1(Seq.empty, BoolT1)))

    val declarationsWithUpdatedPreds = modWithPreds.module.declarations
      .map(decl =>
        decl.name match {
          case newInit.name   => newInit
          case newNext.name   => newNext
          case newLoopOK.name => newLoopOK
          case _              => decl
        })

    // replace each formula by formula == loopOK => formulaInitVar
    // note: this needs to be after the loopOK predicate in the TLA module, since it depends on it
    // this reuses the name of 'formula' so we don't have to change the invariant in the checker
    val newFormulas = formulas.zip(exVarDecls).map { case (formula, exVarDecl) =>
      formula.copy(body = builder.impl(loopOKopApp, builder.varDeclAsNameEx(exVarDecl)))
    }

    val declarationsWithoutFormulas = declarationsWithUpdatedPreds
      .filterNot(decl => formulas.exists(formula => formula.name == decl.name))

    // the order of declarations should be safe, but sorting doesn't hurt
    new DeclarationSorter()(modWithPreds.module.copy(
            declarations = varDecls ++
              declarationsWithoutFormulas ++
              newFormulas
        ))
  }

  /**
   * Encodes a given formula, using the Tableau encoding by adjusting init, next, loopOK and the given formula.
   */
  def singleTemporalToInvariant(formula: TlaOperDecl): (Seq[TlaVarDecl], PredExs, TlaVarDecl) = {

    var (varDecls, preds, (formulaEx)) = encodeSyntaxTreeInPredicates(formula.body)

    // create a new variable that stores whether the formula evaluated to true in the first state
    // this is necessary because a temporal formula on a sequence of states should be satisfied
    // if it holds in the first state, so we need to remember this information
    val exVarDecl = new TlaVarDecl("__" + formula.name + "_init")(Typed(BoolT1))
    val exVar = builder.varDeclAsNameEx(exVarDecl)

    // __foo_init = [inital evaluation of foo]
    val initExVarEx = builder.eql(
        exVar,
        builder.useTrustedEx(formulaEx),
    )

    // UNCHANGED << __foo_init >>
    val nextExVarEx = builder.unchanged(exVar)

    (
        varDecls :+ exVarDecl,
        preds ++ PredExs(
            initExs = Seq(initExVarEx),
            nextExs = Seq(nextExVarEx),
        ),
        exVarDecl,
    )
  }

  /**
   * Moves down the syntax tree of a provided expression curNode. Each node of the syntax tree that has temporal level,
   * e.g. contains temporal operators somewhere below it, is encoded by a variable __temporal_curNode. For example, for
   * the formula [](A => <>B), The syntax tree has the shape
   * {{{
   *   box
   *    |
   *    =>
   *   /  \
   *  A   diamond
   *         |
   *         B
   * }}}
   * Assuming A and B do not contain temporal operators, new variables are introduced for all nodes above them, that is
   * var_BoxAImpliesDiamondB, var_AImpliesDiamondB, var_DiamondB The value of each variable in a given state corresponds
   * to a commitment whether or not the formula corresponding to this variable holds true at that point in the trace.
   * For example, if var_DiamondB is true in a state, the spec will ensure that in some future state, B holds (recall
   * that B holding at some point in the future is the definition of <>B).
   * @return
   */
  def encodeSyntaxTreeInPredicates(curNode: TlaEx): (Seq[TlaVarDecl], PredExs, TBuilderInstruction) = {
    levelFinder.getLevelOfExpression(Set.empty, curNode) match {
      case TlaLevelTemporal =>
        curNode match {
          case NullEx =>
            throw new IrrecoverablePreprocessingError(
                "Found a null expression of temporal level; this should not be possible.")
          case NameEx(_) =>
            throw new IrrecoverablePreprocessingError(
                "Found a name expression of temporal level.  After inlining no such name expressions should be left in the predicate!")
          case ValEx(_) =>
            throw new IrrecoverablePreprocessingError(
                "Found a value expression of temporal level. This should not be possible.")
          case LetInEx(_, _) =>
            throw new IrrecoverablePreprocessingError(
                "Expected to find no LET-IN expressions. They should have been rewritten by the inliner.")
          case OperEx(oper, args @ _*) =>
            val nodeIdentifier = TableauEncoder.NAME_PREFIX + gen.newName()

            /* create a new variable for this node.
            e.g.
            \* @type: Bool;
            __temporal_curNode
             */

            val nodeVarDecl = new TlaVarDecl(nodeIdentifier)(Typed(BoolT1))

            /* create a new loop variable for this node
            e.g.
            \* @type: Bool;
            __saved___temporal_curNode
             */
            val nodeLoopVarDecl = loopEnc.createVarCopyVariableInLoop(nodeVarDecl)

            val nodeVarEx = builder.varDeclAsNameEx(nodeVarDecl)
            val nodeLoopVarEx = builder.varDeclAsNameEx(nodeLoopVarDecl)

            varNamesToExStrings = varNamesToExStrings + ((nodeVarDecl.name, curNode.toString().replace("\"", "\'")))
            varNamesToExStrings = varNamesToExStrings + ((nodeLoopVarDecl.name, curNode.toString().replace("\"", "\'")))

            // creates the expressions that should be present for both temporal and non-temporal node variables
            val genericPredExs = createGenericNodeVarExs(nodeVarEx, nodeLoopVarEx)

            /* encode the arguments of the node
             */
            val (argVarDecls, argsPreds: Seq[PredExs], argExs: Seq[TBuilderInstruction]) = args
              .map(arg => {
                encodeSyntaxTreeInPredicates(arg)
              })
              .unzip3

            val argsPredsUnion = argsPreds.foldLeft(genericPredExs)(_ ++ _)

            /* encode the node itself
             */
            oper match {
              case TlaTempOper.box | TlaTempOper.diamond => /* curNode has the form []A or <>A */
                /* create new auxiliary variable curNode_unroll or curNode_finally */
                val nameSuffix = oper match {
                  case TlaTempOper.box     => TableauEncoder.BOX_SUFFIX
                  case TlaTempOper.diamond => TableauEncoder.DIAMOND_SUFFIX
                }
                val auxVarDecl = new TlaVarDecl(nodeIdentifier + nameSuffix)(Typed(BoolT1))

                val auxVarEx = builder.varDeclAsNameEx(auxVarDecl)
                val auxVarExPrime = builder.prime(auxVarEx)

                /*
                  initialize __temporal_curNode

                  /\ __temporal_curNode \in BOOLEAN
                  /\ __temporal_curNode_globally = TRUE or /\ __temporal_curNode_finally = FALSE
                 */
                val initialValue = oper match {
                  case TlaTempOper.box     => true
                  case TlaTempOper.diamond => false
                }
                val auxVarInitEx = builder.eql(auxVarEx, builder.bool(initialValue))

                /* update __temporal_curNode:

                  /\ __temporal_curNode' \in BOOLEAN
                  /\ __temporal_curNode_globally' \in BOOLEAN or __temporal_curNode_finally' \in BOOLEAN

                                           outerOp                                          outerOp
                  /\ __temporal_curNode <=> A /\ __temporal_curNode' or __temporal_curNode <=> A \/ __temporal_curNode'

                                                    outerOp
                  /\ __temporal_curNode_globally' <=> /\ __temporal_curNode_globally
                                                      /\ (~InLoop' \/ A')
                                                    outerOp      innerOp
                  or
                                                   outerOp
                  /\ __temporal_curNode_finally' <=>  \/ __temporal_curNode_finally
                                                      \/  (InLoop' /\ A')
                                                    outerOp      innerOp
                 */

                /*
                box and diamond differ in the inner and outer operators,
                and whether the InLoop variable is negated in the conjunction
                 */
                val (outerOpTmp, innerOpTmp, innerInLoopEx) = oper match {
                  case TlaTempOper.box     => (builder.and _, builder.or _, builder.not(loopEnc.inLoopPrime))
                  case TlaTempOper.diamond => (builder.or _, builder.and _, loopEnc.inLoopPrime)
                }

                /*
                outerOpTmp and innerOpTmp expect Seq[TBuilderInstruction] instead of TBuilderInstruction*,
                so define new operators here to take TBuilderInstruction*
                 */
                def outerOp(args: TBuilderInstruction*): TBuilderInstruction = outerOpTmp(args)
                def innerOp(args: TBuilderInstruction*): TBuilderInstruction = innerOpTmp(args)

                /* __temporal_curNode_unroll' \in BOOLEAN */
                val auxVarUpdateAssignmentEx = inBoolSet(builder.prime(auxVarEx))

                /* __temporal_curNode <=> A /\ __temporal_curNode' */
                val nodeVarUpdateConditionEx = builder.equiv(
                    nodeVarEx,
                    outerOp(
                        argExs(0),
                        builder.prime(nodeVarEx),
                    ),
                )

                /* __temporal_curNode_unroll' <=>   /\ __temporal_curNode_unroll
                                                    /\ (~InLoop' \/ A')
                 */
                val auxVarUpdateConditionEx = builder.equiv(
                    auxVarExPrime,
                    outerOp(
                        auxVarEx,
                        innerOp(
                            innerInLoopEx,
                            builder.prime(argExs(0)),
                        ),
                    ),
                )

                /* update loopOK:
                  (__temporal_curNode_unroll => __temporal_curNode) or (__temporal_curNode => __temporal_curNode_finally)
                 */
                val auxVarLoopOKEx =
                  oper match {
                    case TlaTempOper.box     => builder.impl(auxVarEx, nodeVarEx)
                    case TlaTempOper.diamond => builder.impl(nodeVarEx, auxVarEx)
                  }

                (
                    Seq(
                        nodeVarDecl,
                        nodeLoopVarDecl,
                        auxVarDecl,
                    ) ++ argVarDecls.flatten,
                    argsPredsUnion ++
                      PredExs(
                          initExs = Seq(
                              auxVarInitEx
                          ),
                          nextExs = Seq(
                              auxVarUpdateAssignmentEx,
                              nodeVarUpdateConditionEx,
                              auxVarUpdateConditionEx,
                          ),
                          loopOKExs = Seq(
                              auxVarLoopOKEx
                          ),
                      ),
                    nodeVarEx,
                )
              case TlaTempOper.leadsTo =>
                throw new LanguagePredError(
                    "Don't know how to handle operator '~>'. It should have been removed by the Desugarer",
                    Seq((curNode.ID, "")))
              case TlaTempOper.guarantees =>
                throw new NotImplementedError("Handling guarantees is not supported yet!")
              case TlaTempOper.strongFairness | TlaTempOper.weakFairness =>
                throw new NotImplementedError("Handling fairness is not supported yet!")
              case TlaTempOper.AA | TlaTempOper.EE =>
                throw new NotImplementedError("Handling temporal quantifiers is not supported yet!")
              case _ => // not a temporal operator. e.g. A /\ B
                /* init and next conditions look like this: __temporal_curNode = __temporal_A /\ __temporal_B */
                val conditionalPredExs = createPropositionalOperNodeExs(nodeVarEx, oper, curNode.typeTag, argExs: _*)

                (
                    Seq(
                        nodeVarDecl,
                        nodeLoopVarDecl,
                    ) ++ argVarDecls.flatten,
                    argsPredsUnion ++ conditionalPredExs,
                    /* expression for this node is the name of the variable that encodes it */
                    nodeVarEx,
                )
            }
          case _ =>
            throw new IrrecoverablePreprocessingError(
                s"Cannot handle expression ${curNode.toString()} of type ${curNode.getClass()}")
        }
      case _ => /* a propositional expression - used as-is in the formula encoding the syntax tree */
        (Seq.empty[TlaVarDecl], PredExs(), builder.useTrustedEx(curNode))
    }
  }

  /**
   * Creates PredExs for a given propositional operator application of the form OperEx(oper, argExs)(typeTag). The
   * nodeVarEx should be the variable for the node in the syntax tree representing the operator application.
   */
  private def createPropositionalOperNodeExs(
      nodeVarEx: TBuilderInstruction,
      oper: TlaOper,
      typeTag: TypeTag,
      argExs: TlaEx*): PredExs = {

    /* initialize the variable for this node
                    e.g. __temporal_curNode = __temporal_A /\ __temporal_B
     */
    val nodeVarInitConditionEx =
      builder.eql(
          nodeVarEx,
          builder.useTrustedEx(OperEx(oper, argExs: _*)(typeTag)),
      )

    /* update the variable for this node
                    e.g. __temporal_curNode' = __temporal_A' /\ __temporal_B'
     */
    val nodeVarUpdateConditionEx = builder.eql(
        builder.prime(nodeVarEx),
        builder.useTrustedEx(OperEx(oper, argExs: _*)(typeTag)),
    )

    PredExs(Seq(nodeVarInitConditionEx), Seq(nodeVarUpdateConditionEx))
  }

  private def createGenericNodeVarExs(
      nodeVarEx: TBuilderInstruction,
      loopNodeVarEx: TBuilderInstruction): PredExs = {
    /* generic initialization for node variable: __temporal_curNode \in BOOLEAN */
    val nodeVarInitAssignmentEx = inBoolSet(nodeVarEx)

    /* generic update for node variable: __temporal_curNode' \in BOOLEAN */
    val nodeVarUpdateAssignmentEx = inBoolSet(builder.prime(nodeVarEx))

    /* initialize loop variable: __saved___temporal_curNode = __temporal_curNode
     */
    val loopVarInitAssignmentEx = builder.eql(
        loopNodeVarEx,
        nodeVarEx,
    )

    /* generic update for loop variable: __saved___temporal_curNode' = IF (InLoop' = InLoop) THEN __saved___temporal_curNode ELSE __temporal_curNode}}}
     */
    val loopVarUpdateAssignmentEx = loopEnc.getLoopVarUpdateEx(nodeVarEx, loopNodeVarEx)

    /* update loopOK
     */
    val loopVarLoopOKEx =
      builder.eql(nodeVarEx, loopNodeVarEx)

    PredExs(
        Seq(
            nodeVarInitAssignmentEx,
            loopVarInitAssignmentEx,
        ),
        Seq(
            nodeVarUpdateAssignmentEx,
            loopVarUpdateAssignmentEx,
        ),
        Seq(
            loopVarLoopOKEx
        ),
    )
  }

}

object TableauEncoder {

  /**
   * A prefix added to the names of all variables used for the tableau encoding. Useful for disambiguating them from
   * variables in the original spec.
   */
  val NAME_PREFIX = "__temporal_"
  val PREDS_TO_VARS_MAPPING_NAME = "__preds_to_vars"
  val BOX_SUFFIX = "_unroll"
  val DIAMOND_SUFFIX = "_unroll"
}
