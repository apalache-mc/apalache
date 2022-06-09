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
    val newFormulas = formulas.zip(exVarDecls).map { case (formula, exVarDecl) =>
      formula.copy(body = builder.impl(loopOKopApp, builder.varDeclAsNameEx(exVarDecl)))
    }

    val declarationsWithoutFormulas = declarationsWithUpdatedPreds
      .filterNot(decl => formulas.exists(formula => formula.name == decl.name))

    modWithPreds.module.copy(
        declarations = varDecls ++
          declarationsWithoutFormulas ++
          newFormulas
    )
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
    val nextExVarEx =
      builder.unchanged(exVar)

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
   * e.g. contains temporal operators somewhere below it, is encoded by a variable curNode_predicate. For example, for
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
            varNamesToExStrings = varNamesToExStrings +
              ((nodeIdentifier, curNode.toString().replace("\"", "\'")))

            /* create a new variable for this node
                    e.g.
                    \* @type: Bool;
                    curNode_predicate
             */
            val nodeVarDecl = new TlaVarDecl(nodeIdentifier)(Typed(BoolT1))

            val nodeVarEx = builder.varDeclAsNameEx(nodeVarDecl)
            val nodeVarExPrime = builder.prime(nodeVarEx)

            /* create a new loop variable for this node
                    e.g.
                    \* @type: Bool;
                    __saved_curNode_predicate
             */
            val nodeLoopVarDecl = loopEnc.createVarCopyVariableInLoop(nodeVarDecl)

            varNamesToExStrings = varNamesToExStrings + ((nodeLoopVarDecl.name, curNode.toString().replace("\"", "\'")))

            /* generic initialization for node variable: curNode_predicate \in BOOLEAN */
            val nodeVarInitAssignmentEx =
              builder.in(nodeVarEx, builder.booleanSet())

            /* generic update for node variable: curNode_predicate' \in BOOLEAN */
            val nodeVarUpdateAssignmentEx =
              builder.in(nodeVarExPrime, builder.booleanSet())

            /* initialize loop variable: __saved_curNode_predicate = curNode_predicate
             */
            val loopVarInitAssignmentEx =
              builder.eql(builder.varDeclAsNameEx(nodeLoopVarDecl), builder.varDeclAsNameEx(nodeVarDecl))

            /* generic update for loop variable: __saved_curNode_predicate' = IF (InLoop' = InLoop) THEN __saved_curNode_predicate ELSE curNode_predicate}}}
             */
            val loopVarUpdateAssignmentEx = loopEnc.getLoopVarUpdateEx(nodeVarDecl, nodeLoopVarDecl)

            /* update loopOK
             */
            val loopVarLoopOKEx =
              builder.eql(builder.varDeclAsNameEx(nodeVarDecl), builder.varDeclAsNameEx(nodeLoopVarDecl))

            /* encode the arguments of the node
             */
            val (argVarDecls, argsPreds: Seq[PredExs], argExs: Seq[TBuilderInstruction]) = args
              .map(arg => {
                encodeSyntaxTreeInPredicates(arg)
              })
              .unzip3

            val argsPredsUnion = argsPreds.foldLeft(PredExs())(_ ++ _)

            /* encode the node itself
             */
            oper match {
              case TlaTempOper.box | TlaTempOper.diamond => /* curNode has the form []A or <>A */
                /* create new auxiliary variable curNode_globally or curNode_finally */
                val nameSuffix = oper match {
                  case TlaTempOper.box     => TableauEncoder.BOX_SUFFIX
                  case TlaTempOper.diamond => TableauEncoder.DIAMOND_SUFFIX
                }
                val auxVarDecl = new TlaVarDecl(nodeIdentifier + nameSuffix)(Typed(BoolT1))

                val auxVarEx = builder.varDeclAsNameEx(auxVarDecl)
                val auxVarExPrime = builder.prime(auxVarEx)

                /*
                  initialize curNode_predicate

                  /\ curNode_predicate \in BOOLEAN
                  /\ curNode_predicate_globally = TRUE or /\ curNode_predicate_finally = FALSE
                 */
                val initialValue = oper match {
                  case TlaTempOper.box     => true
                  case TlaTempOper.diamond => false
                }

                val auxVarInitEx =
                  builder.eql(
                      auxVarEx,
                      builder.bool(initialValue),
                  )

                /* update curNode_predicate:

                  /\ curNode_predicate' \in BOOLEAN
                  /\ curNode_predicate_globally' \in BOOLEAN or curNode_predicate_finally' \in BOOLEAN

                                           outerOp                                          outerOp
                  /\ curNode_predicate <=> A /\ curNode_predicate' or curNode_predicate <=> A \/ curNode_predicate'

                                                    outerOp
                  /\ curNode_predicate_globally' <=>  /\ curNode_predicate_globally
                                                      /\ (~InLoop' \/ A')
                                                    outerOp      innerOp
                  or
                                                   outerOp
                  /\ curNode_predicate_finally' <=>   \/ curNode_predicate_finally
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

                /* curNode_predicate' \in BOOLEAN */
                val nodeVarUpdateAssignmentEx = builder.in(
                    nodeVarExPrime,
                    builder.booleanSet(),
                )

                /* curNode_predicate_globally' \in BOOLEAN */
                val auxVarUpdateAssignmentEx = builder.in(
                    builder.prime(auxVarEx),
                    builder.booleanSet(),
                )

                /* curNode_predicate <=> A /\ curNode_predicate' */
                val nodeVarUpdateConditionEx = builder.equiv(
                    nodeVarEx,
                    outerOp(
                        argExs(0),
                        nodeVarExPrime,
                    ),
                )

                /* curNode_predicate_globally' <=>  /\ curNode_predicate_globally
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
                  (curNode_predicate_globally => curNode_predicate) or (curNode_predicate => curNode_predicate_finally)
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
                            nodeVarInitAssignmentEx,
                            loopVarInitAssignmentEx,
                            auxVarInitEx,
                        ),
                        nextExs = Seq(
                            nodeVarUpdateAssignmentEx,
                            loopVarUpdateAssignmentEx,
                            auxVarUpdateAssignmentEx,
                            nodeVarUpdateConditionEx,
                            auxVarUpdateConditionEx,
                        ),
                        loopOKExs = Seq(
                            loopVarLoopOKEx,
                            auxVarLoopOKEx,
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
                /* initialize the variable for this node
                    e.g. curNode_predicate = A_predicate /\ B_predicate
                 */
                val nodeVarInitConditionEx =
                  builder.eql(
                      nodeVarEx,
                      builder.useTrustedEx(OperEx(oper, argExs: _*)(curNode.typeTag)),
                  )

                /* update the variable for this node
                    e.g. curNode_predicate' = A_predicate' /\ B_predicate'
                 */
                val nodeVarUpdateConditionEx = builder.eql(
                    nodeVarExPrime,
                    builder.useTrustedEx(OperEx(oper, argExs: _*)(curNode.typeTag)),
                )

                (
                    Seq(
                        nodeVarDecl,
                        nodeLoopVarDecl,
                    ) ++ argVarDecls.flatten,
                    argsPredsUnion ++ PredExs(
                        initExs = Seq(
                            nodeVarInitAssignmentEx,
                            loopVarInitAssignmentEx,
                            nodeVarInitConditionEx,
                        ),
                        nextExs = Seq(
                            nodeVarUpdateAssignmentEx,
                            loopVarUpdateAssignmentEx,
                            nodeVarUpdateConditionEx,
                        ),
                        loopOKExs = Seq(
                            loopVarLoopOKEx
                        ),
                    ),
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
