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

/**
 * Encode temporal operators.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TableauEncoder(module: TlaModule, gen: UniqueNameGenerator, loopEnc: LoopEncoder) extends LazyLogging {
  val levelFinder = new TlaLevelFinder(module)
  val varNamesToExStrings = new HashMap[String, String]()

  def encodeVarNameMapping(modWithPreds: ModWithPreds): ModWithPreds = {
    val varNameSets = varNamesToExStrings.map { case (key, value) =>
      builder.enumSet(builder.str(key), builder.str(value))
    }.toSeq

    val mapDecl =
      new TlaOperDecl(
          "GenVarNamesToExFun",
          List.empty,
          builder.enumSet(
              varNameSets: _*
          ),
      )(Typed(SetT1))

    val newModule = new TlaModule(modWithPreds.module.name, modWithPreds.module.declarations :+ mapDecl)
    modWithPreds.setModule(newModule)
  }

  def encodeInvariants(
      modWithPreds: ModWithPreds,
      invariants: Seq[TlaOperDecl]): ModWithPreds = {

    encodeVarNameMapping(invariants.foldLeft(modWithPreds)(encodeInvariant))
  }

  def encodeInvariant(
      modWithPreds: ModWithPreds,
      invariant: TlaOperDecl): ModWithPreds = {

    encodeSyntaxTreeInPredicates(modWithPreds, invariant.body)._1
  }

  def insertAt[T](elem: T, seq: Seq[T], pos: Int): Seq[T] = {
    seq.take(pos) ++ List(elem) ++ seq.drop(pos)
  }

  def getAuxVarForTempOper(oper: TlaTempOper, nodeIdentifier: String): TlaVarDecl = {
    val nameSuffix = oper match {
      case TlaTempOper.box     => "_globally"
      case TlaTempOper.diamond => "_eventually"
    }

    new TlaVarDecl(nodeIdentifier + nameSuffix)(Typed(BoolT1()))
  }

  def encodeSyntaxTreeInPredicates(
      modWithPreds: ModWithPreds,
      curNode: TlaEx): (ModWithPreds, TlaEx) = {
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
          case LetInEx(_, _) =>
            throw new IrrecoverablePreprocessingError(
                "Expect to find no LET-IN expressions. They should have been rewritten by the inliner")
          case OperEx(oper, args @ _*) =>
            var curModWithPreds = modWithPreds

            val nodeIdentifier = gen.newName()
            varNamesToExStrings.addOne(nodeIdentifier, curNode.toString().replace("\"", "\'"))
            varNamesToExStrings.addOne("loop_" + nodeIdentifier, curNode.toString().replace("\"", "\'"))

            /* create a new variable for this node
                    e.g.
                    \* @type: Bool;
                    curNode_predicate
             */
            val nodeVarDecl = new TlaVarDecl(nodeIdentifier)(curNode.typeTag)
            curModWithPreds = curModWithPreds.prependDecl(nodeVarDecl)
            val nodeVarEx = builder.declAsNameEx(nodeVarDecl)
            val nodeVarExPrime = builder.primeVar(nodeVarDecl)

            /* create a new loop variable for this node
                    e.g.
                    \* @type: Bool;
                    Loop_curNode_predicate
             */
            val nodeLoopVarDecl = new TlaVarDecl(s"Loop_${nodeIdentifier}")(curNode.typeTag)
            curModWithPreds = curModWithPreds.prependDecl(nodeLoopVarDecl)

            /* initialize loop variable
             */
            val initWithLoopVar = loopEnc.addLoopVarToInit(nodeVarDecl, nodeLoopVarDecl, modWithPreds.init)

            /* update loop variable
             */
            val nextWithLoopVar = loopEnc.addLoopVarToNext(nodeVarDecl, nodeLoopVarDecl, modWithPreds.next)

            /* update loopOK
             */
            val loopOKWithLoopVar = loopEnc.addVariableToLoopOK(nodeVarDecl, nodeLoopVarDecl, modWithPreds.loopOK)

            curModWithPreds = curModWithPreds.setPredicates(initWithLoopVar, nextWithLoopVar, loopOKWithLoopVar)

            /* encode the arguments of the node
             */
            val argExs = args.map(arg => {
              val modWithPredsAndArgEx = encodeSyntaxTreeInPredicates(curModWithPreds, arg)
              curModWithPreds = modWithPredsAndArgEx._1
              val argEx = modWithPredsAndArgEx._2
              builder.createUnsafeInstruction(argEx)
            })

            /* encode the node itself
             */
            oper match {
              case TlaTempOper.box | TlaTempOper.diamond => /* curNode has the form []A or <>A */
                /* create new auxiliary variable curNode_globally or curNode_finally */
                val auxVarDecl = getAuxVarForTempOper(oper.asInstanceOf[TlaTempOper], nodeIdentifier)
                val auxVarEx = builder.declAsNameEx(auxVarDecl)
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

                val newInit = conjunctExToOperDecl(
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
                                                      \/  (~InLoop' /\ A')
                                                    outerOp      innerOp
                 */

                /*
                box and diamond differ in the inner and outer operators
                 */
                val (outerOpTmp, innerOpTmp) = oper match {
                  case TlaTempOper.box     => (builder.and _, builder.or _)
                  case TlaTempOper.diamond => (builder.or _, builder.and _)
                }

                /*
                outerOpTmp and innerOpTmp expect Seq[TBuilderInstruction] instead of TBuilderInstruction*,
                so define new operators here to take TBuilderInstruction*
                 */
                def outerOp(args: TBuilderInstruction*): TBuilderInstruction = outerOpTmp(args)
                def innerOp(args: TBuilderInstruction*): TBuilderInstruction = innerOpTmp(args)

                val newNext = conjunctExToOperDecl(
                    builder.and(
                        /* curNode_predicate' \in BOOLEAN */
                        builder.in(
                            nodeVarExPrime,
                            builder.booleanSet(),
                        ),
                        /* curNode_predicate_globally' \in BOOLEAN */
                        builder.in(
                            auxVarEx,
                            builder.booleanSet(),
                        ),

                        /* curNode_predicate <=> A /\ curNode_predicate' */
                        builder.equiv(
                            nodeVarEx,
                            outerOp(
                                argExs(0),
                                nodeVarExPrime,
                            ),
                        ),
                        /* curNode_predicate_globally' <=>  /\ curNode_predicate_globally
                                                            /\ (~InLoop' \/ A')
                         */
                        builder.equiv(
                            nodeVarExPrime,
                            outerOp(
                                nodeVarEx,
                                innerOp(
                                    loopEnc.inLoopPrime,
                                    builder.prime(argExs(0)),
                                ),
                            ),
                        ),
                    ),
                    curModWithPreds.next,
                )

                /* update loopOK:
                  (curNode_predicate_globally => curNode_predicate) or (curNode_predicate => curNode_predicate_finally)
                 */
                val newLoopOK = conjunctExToOperDecl(
                    oper match {
                      case TlaTempOper.box     => builder.impl(auxVarEx, nodeVarEx)
                      case TlaTempOper.diamond => builder.impl(nodeVarEx, auxVarEx)
                    },
                    curModWithPreds.loopOK,
                )

                curModWithPreds = curModWithPreds.setPredicates(newInit, newNext, newLoopOK)
                (curModWithPreds, nodeVarEx)
              // case TlaTempOper.guarantees     => mkOpApp("%%s %s %%s".format(m_guarantee), args: _*)
              // case TlaTempOper.leadsTo        => mkOpApp("%%s %s %%s".format(m_leadsto), args: _*)
              // case TlaTempOper.strongFairness => mkApp("SF_%s(%s)", args: _*)
              // case TlaTempOper.weakFairness   => mkApp("WF_%s(%s)", args: _*)
              // case TlaTempOper.AA             => mkOpApp("[%s]%%s . %%s".format(m_forall), args: _*)
              // case TlaTempOper.EE             => mkOpApp("[%s]%%s . %%s".format(m_exists), args: _*)

              case _ => // not a temporal operator. e.g. A /\ B
                /* initialize the variable for this node
                    e.g. newInit ==
                          /\ oldInit
                          /\ curNode_predicate = A_predicate /\ B_predicate
                 */
                val newInit = conjunctExToOperDecl(
                    builder.eql(
                        nodeVarEx,
                        builder.createUnsafeInstruction(OperEx(oper, argExs: _*)(curNode.typeTag)),
                    ),
                    curModWithPreds.init,
                )
                /* update the variable for this node
                    e.g. newNext ==
                          /\ oldNext
                          /\ curNode_predicate' = A_predicate' /\ B_predicate'
                 */
                val newNext = conjunctExToOperDecl(
                    builder.eql(
                        nodeVarExPrime,
                        builder.createUnsafeInstruction(OperEx(oper, argExs: _*)(curNode.typeTag)),
                    ),
                    curModWithPreds.next,
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
      case _ => /* a propositional expression - used as-is in the formula encoding the syntax tree */
        (modWithPreds, curNode)
    }
  }

}

object TableauEncoder {
  val NAME_PREFIX = ""
}
