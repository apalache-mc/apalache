package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import scalaz.Scalaz.{init => _}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.tla.pp.IrrecoverablePreprocessingError
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import at.forsyte.apalache.tla.pp.temporal.ScopedBuilderExtensions._
import at.forsyte.apalache.tla.pp.temporal.DeclUtils._
import scala.collection.mutable.HashMap
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
  val varNamesToExStrings = new HashMap[String, String]()

  /**
   * Encodes each of a sequence of temporal formulas.
   * @see
   *   [[encodeFormula]]
   */
  def temporalsToInvariants(
      modWithPreds: ModWithPreds,
      formulas: Seq[TlaOperDecl]): ModWithPreds = {

    formulas.foldLeft(modWithPreds)(singleTemporalToInvariant)
  }

  /**
   * Adds a variable that stores the initial value of the given expression ex. Create a new variable Init_ex and modify
   * init and next:
   *
   * newInit == oldInit /\ Init_ex = ex
   *
   * newNext == oldNext /\ UNCHANGED << Init_ex >>
   */
  def addInitExVar(modWithPreds: ModWithPreds, ex: TlaEx, exName: String): (ModWithPreds, TlaVarDecl) = {
    val exVarDecl = new TlaVarDecl("__" + exName + "_init")(Typed(BoolT1))
    val exVar = builder.declAsNameEx(exVarDecl)

    val newInit = andInDecl(
        builder.eql(
            exVar,
            builder.useTrustedEx(ex),
        ),
        modWithPreds.init,
        tracker,
    )

    val newNext = andInDecl(
        builder.unchanged(exVar),
        modWithPreds.next,
        tracker,
    )

    val curModWithPreds = modWithPreds.setPredicates(newInit, newNext, modWithPreds.loopOK)
    (curModWithPreds.prependDecl(exVarDecl), exVarDecl)
  }

  /**
   * Encodes a given formula, using the Tableau encoding by adjusting init, next, loopOK and the given formula.
   */
  def singleTemporalToInvariant(
      modWithPreds: ModWithPreds,
      formula: TlaOperDecl): ModWithPreds = {

    var (curModWithPreds, formulaEx) = encodeSyntaxTreeInPredicates(modWithPreds, formula.body)

    val tuple = addInitExVar(curModWithPreds, formulaEx, formula.name)
    curModWithPreds = tuple._1
    val initExVarDecl = tuple._2

    // replace formula by formula == loopOK => formula_init, and move formula to the end of the spec so it is after loopOK
    val newFormulaDecl = new TlaOperDecl(
        formula.name,
        formula.formalParams,
        builder.impl(
            builder.appOp(builder.declAsNameEx(curModWithPreds.loopOK), Seq.empty[TBuilderInstruction]: _*),
            builder.declAsNameEx(initExVarDecl),
        ),
    )(formula.typeTag)
    val newDecls = curModWithPreds.module.declarations.filterNot(decl => decl.name == formula.name) :+ newFormulaDecl
    val newModule = new TlaModule(curModWithPreds.module.name, newDecls)

    curModWithPreds.setModule(newModule)
  }

  /**
   * Takes a temporal operator and a name, and generates a new variable declaration declaring the auxiliary "unrolling"
   * variable for that temporal operator.
   */
  private def createUnrollingVar(oper: TlaTempOper, nodeIdentifier: String): TlaVarDecl = {
    val nameSuffix = oper match {
      case TlaTempOper.box     => TableauEncoder.BOX_SUFFIX
      case TlaTempOper.diamond => TableauEncoder.DIAMOND_SUFFIX
    }

    new TlaVarDecl(nodeIdentifier + nameSuffix)(Typed(BoolT1))
  }

  /**
   * Takes a set of names that represent the names defined by let-in operators, and identifies which of those names
   * appear in the given expression.
   */
  private def findLetVariablesInSubtree(ex: TlaEx, letInNames: Set[String]): Set[String] = {
    ex match {
      case LetInEx(_, decls @ _*) =>
        decls.foldLeft(
            Set.empty[String]
        )((acc, operDecl) => findLetVariablesInSubtree(operDecl.body, letInNames).union(acc))
      case ValEx(_)     => return Set.empty
      case NameEx(name) => if (letInNames.contains(name)) return Set(name) else return Set.empty
      case OperEx(_, args @ _*) =>
        args.foldLeft(Set.empty[String])((acc, argEx) => findLetVariablesInSubtree(argEx, letInNames).union(acc))
      case NullEx => return Set.empty
    }
  }

  /**
   * Wraps a given expression with all Let-In expressions, from among the provided map, whose names appear in the
   * expression
   */
  private def wrapWithLetIn(ex: TlaEx, letInMap: Map[String, TlaEx]): TlaEx = {
    val letInNamesInSubtree = findLetVariablesInSubtree(ex, letInMap.keySet)
    val letInDecls = letInNamesInSubtree.map(name => {
      // TODO: wrap the body of the let in with the let ins needed in it, if any
      val declBody = letInMap.get(name).get

      TlaOperDecl(
          name,
          List.empty,
          letInMap.get(name).get,
      )(
          letInMap.get(name).get.typeTag
      )
    })
    builder.multiLetIn(ex, letInDecls.toSeq: _*)
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
   *
   * @param letInContext
   *   a mapping from operator names to the expressions they represent. Should only be unary operators. Empty by
   *   default.
   */
  def encodeSyntaxTreeInPredicates(
      modWithPreds: ModWithPreds,
      curNode: TlaEx,
      letInContext: Map[String, TlaEx] = Map[String, TlaEx]()): (ModWithPreds, TlaEx) = {
    print("curNode: " + curNode.toString() + "\n" + curNode.getClass() + "\n------------\n")
    levelFinder.getLevelOfExpression(Set.empty, curNode) match {
      case TlaLevelTemporal =>
        curNode match {
          case NullEx =>
            throw new IrrecoverablePreprocessingError(
                "Found a null expression of temporal level; this should not be possible")
          case NameEx(_) =>
            throw new IrrecoverablePreprocessingError(
                "Found a name expression of temporal level.  After inlining no such name expressions should be left in the predicate!")
          case ValEx(_) =>
            throw new IrrecoverablePreprocessingError(
                "Found a value expression of temporal level. This should not be possible.")
          case LetInEx(body, TlaOperDecl(letInName, args, letInEx)) =>
            if (!args.isEmpty) {
              throw new IrrecoverablePreprocessingError("Expect to find only unary LET-IN expressions. " +
                "Non-unary LET-IN expressions " +
                "should have been rewritten by the inliner")
            }

            val newLetInContext =
              letInContext + ((letInName, letInEx))

            encodeSyntaxTreeInPredicates(
                modWithPreds,
                body,
                newLetInContext,
            )
          case OperEx(oper, args @ _*) =>
            var curModWithPreds = modWithPreds

            val nodeIdentifier = TableauEncoder.NAME_PREFIX + gen.newName()
            varNamesToExStrings.addOne(nodeIdentifier, curNode.toString().replace("\"", "\'"))

            /* create a new variable for this node
                    e.g.
                    \* @type: Bool;
                    curNode_predicate
             */
            val nodeVarDecl = new TlaVarDecl(nodeIdentifier)(Typed(BoolT1))
            curModWithPreds = curModWithPreds.prependDecl(nodeVarDecl)
            val nodeVarEx = builder.declAsNameEx(nodeVarDecl)
            val nodeVarExPrime = builder.primeVar(nodeVarDecl)

            /* create a new loop variable for this node
                    e.g.
                    \* @type: Bool;
                    __saved_curNode_predicate
             */
            val nodeLoopVarDecl = loopEnc.createVarCopyVariableInLoop(nodeVarDecl)
            varNamesToExStrings.addOne(nodeLoopVarDecl.name, curNode.toString().replace("\"", "\'"))

            curModWithPreds = curModWithPreds.prependDecl(nodeLoopVarDecl)

            /* generic initialization for node variable: curNode_predicate \in BOOLEAN */
            val initWithNodeVar =
              andInDecl(builder.in(nodeVarEx, builder.booleanSet()), modWithPreds.init, tracker)

            /* generic update for node variable: curNode_predicate' \in BOOLEAN */
            val nextWithNodeVar =
              andInDecl(builder.in(nodeVarExPrime, builder.booleanSet()), modWithPreds.next, tracker)

            /* initialize loop variable
             */
            val initWithLoopVar = loopEnc.addLoopVarToInit(nodeVarDecl, nodeLoopVarDecl, initWithNodeVar)

            /* update loop variable
             */
            val nextWithLoopVar = loopEnc.addLoopVarToNext(nodeVarDecl, nodeLoopVarDecl, nextWithNodeVar)

            /* update loopOK
             */
            val loopOKWithLoopVar = loopEnc.addVariableToLoopOK(nodeVarDecl, nodeLoopVarDecl, modWithPreds.loopOK)

            curModWithPreds = curModWithPreds.setPredicates(initWithLoopVar, nextWithLoopVar, loopOKWithLoopVar)

            /* encode the arguments of the node
             */
            val argExs = args
              .map(arg => {
                val modWithPredsAndArgEx =
                  encodeSyntaxTreeInPredicates(
                      curModWithPreds,
                      arg,
                      letInContext,
                  )
                curModWithPreds = modWithPredsAndArgEx._1
                val argEx = modWithPredsAndArgEx._2
                builder.useTrustedEx(argEx)
              })
              // wraps argument expressions with the necessary let-in expressions, if any appear in them
              // this is necessary because the syntax tree is 'carved up' into individual nodes,
              // and the let-in expressions may be very far from where they are used
              .map(ex => builder.useTrustedEx(wrapWithLetIn(ex, letInContext)))

            /* encode the node itself
             */
            oper match {
              case TlaTempOper.box | TlaTempOper.diamond => /* curNode has the form []A or <>A */
                /* create new auxiliary variable curNode_globally or curNode_finally */
                val auxVarDecl = createUnrollingVar(oper.asInstanceOf[TlaTempOper], nodeIdentifier)
                val auxVarEx = builder.declAsNameEx(auxVarDecl)
                val auxVarExPrime = builder.prime(auxVarEx)
                curModWithPreds = curModWithPreds.prependDecl(auxVarDecl)

                /* update init:
                  newInit ==
                  /\ oldInit
                  /\ curNode_predicate \in BOOLEAN
                  /\ curNode_predicate_globally = TRUE or /\ curNode_predicate_finally = FALSE
                 */
                val initialValue = oper match {
                  case TlaTempOper.box     => true
                  case TlaTempOper.diamond => false
                }

                val newInit = andInDecl(
                    builder.and(
                        builder.in(
                            nodeVarEx,
                            builder.booleanSet(),
                        ),
                        builder.eql(
                            auxVarEx,
                            builder.bool(initialValue),
                        ),
                    ),
                    curModWithPreds.init,
                    tracker,
                )

                /* update next:
                  newNext ==
                  /\ oldNext
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
                val curNodeAssignment = builder.in(
                    nodeVarExPrime,
                    builder.booleanSet(),
                )

                var newNext = andInDecl(
                    curNodeAssignment,
                    curModWithPreds.next,
                    tracker,
                )

                /* curNode_predicate_globally' \in BOOLEAN */
                val auxVarAssignment = builder.in(
                    builder.prime(auxVarEx),
                    builder.booleanSet(),
                )

                newNext = andInDecl(
                    auxVarAssignment,
                    curModWithPreds.next,
                    tracker,
                )

                /* curNode_predicate <=> A /\ curNode_predicate' */
                val curNodeCondition = builder.equiv(
                    nodeVarEx,
                    outerOp(
                        argExs(0),
                        nodeVarExPrime,
                    ),
                )

                newNext = andInDecl(
                    curNodeCondition,
                    curModWithPreds.next,
                    tracker,
                )

                /* curNode_predicate_globally' <=>  /\ curNode_predicate_globally
                                                            /\ (~InLoop' \/ A')
                 */
                val auxVarCondition = builder.equiv(
                    auxVarExPrime,
                    outerOp(
                        auxVarEx,
                        innerOp(
                            innerInLoopEx,
                            builder.prime(argExs(0)),
                        ),
                    ),
                )

                newNext = andInDecl(
                    auxVarCondition,
                    newNext,
                    tracker,
                )

                /* update loopOK:
                  (curNode_predicate_globally => curNode_predicate) or (curNode_predicate => curNode_predicate_finally)
                 */
                val newLoopOK = andInDecl(
                    oper match {
                      case TlaTempOper.box     => builder.impl(auxVarEx, nodeVarEx)
                      case TlaTempOper.diamond => builder.impl(nodeVarEx, auxVarEx)
                    },
                    curModWithPreds.loopOK,
                    tracker,
                )

                curModWithPreds = curModWithPreds.setPredicates(newInit, newNext, newLoopOK)
                (curModWithPreds, nodeVarEx)
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
                    e.g. newInit ==
                          /\ oldInit
                          /\ curNode_predicate = A_predicate /\ B_predicate
                 */
                val newInit = andInDecl(
                    builder.eql(
                        nodeVarEx,
                        builder.useTrustedEx(OperEx(oper, argExs: _*)(curNode.typeTag)),
                    ),
                    curModWithPreds.init,
                    tracker,
                )
                /* update the variable for this node
                    e.g. newNext ==
                          /\ oldNext
                          /\ curNode_predicate' = A_predicate' /\ B_predicate'
                 */
                val newNext = andInDecl(
                    builder.eql(
                        nodeVarExPrime,
                        builder.useTrustedEx(OperEx(oper, argExs: _*)(curNode.typeTag)),
                    ),
                    curModWithPreds.next,
                    tracker,
                )

                curModWithPreds = curModWithPreds.setPredicates(newInit, newNext, curModWithPreds.loopOK)

                (
                    curModWithPreds,
                    /* expression for this node is the name of the variable that encodes it */
                    nodeVarEx,
                )
            }
          case _ =>
            throw new IrrecoverablePreprocessingError(
                s"Cannot handle expression ${curNode.toString()} of type ${curNode.getClass()}")
        }
      case _ => /* a propositional expression -
      used almost as-is in the formula encoding the syntax tree.
      the expression is wrapped with let-in expressions whose names appear in it.
      This is necessary because the syntax tree is 'carved up' into individual nodes,
      and the let-in expressions may be very far from where they are used. */
        (modWithPreds, wrapWithLetIn(curNode, letInContext))
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
