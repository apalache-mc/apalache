package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import scalaz.Scalaz.{init => _, _}
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.tla.pp.IrrecoverablePreprocessingError
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import at.forsyte.apalache.tla.pp.temporal.ScopedBuilderExtensions._
import at.forsyte.apalache.tla.pp.temporal.DeclUtils._

/**
 * Encode temporal operators.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TableauEncoder(module: TlaModule, gen: UniqueNameGenerator, loopEnc: LoopEncoder) extends LazyLogging {
  val levelFinder = new TlaLevelFinder(module)

  def encodeInvariant(
      modWithPreds: ModWithPreds,
      invariant: TlaOperDecl): ModWithPreds = {

    encodeSyntaxTreeInPredicates(modWithPreds, invariant.body)._1
  }

  def insertAt[T](elem: T, seq: Seq[T], pos: Int): Seq[T] = {
    seq.take(pos) ++ List(elem) ++ seq.drop(pos)
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

            /* create a new variable for this node
                    e.g.
                    \* @type: Bool;
                    curNode_predicate
             */
            val nodeVarDecl = new TlaVarDecl(gen.newName())(curNode.typeTag)

            /* create a new loop variable for this node
                    e.g.
                    \* @type: Bool;
                    Loop_curNode_predicate
             */
            val nodeLoopVarDecl = new TlaVarDecl(gen.newName())(curNode.typeTag)

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
              argEx
            })

            /* encode the node itself
             */
            oper match {
              // case TlaTempOper.AA             => mkOpApp("[%s]%%s . %%s".format(m_forall), args: _*)
              // case TlaTempOper.box            => mkOpApp("%s%%s".format(m_box), args: _*)
              // case TlaTempOper.diamond        => mkOpApp("%s%%s".format(m_diamond), args: _*)
              // case TlaTempOper.EE             => mkOpApp("[%s]%%s . %%s".format(m_exists), args: _*)
              // case TlaTempOper.guarantees     => mkOpApp("%%s %s %%s".format(m_guarantee), args: _*)
              // case TlaTempOper.leadsTo        => mkOpApp("%%s %s %%s".format(m_leadsto), args: _*)
              // case TlaTempOper.strongFairness => mkApp("SF_%s(%s)", args: _*)
              // case TlaTempOper.weakFairness   => mkApp("WF_%s(%s)", args: _*)

              case _ => // not a temporal operator. e.g. A /\ B
                /* initialize the variable for this node
                    e.g. newInit ==
                          /\ oldInit
                          /\ curNode_predicate = A_predicate /\ B_predicate
                 */
                val newInit = conjunctExToOperDecl(
                    builder.eql(
                        builder.declAsNameEx(nodeVarDecl),
                        builder.createUnsafeInstruction(OperEx(oper, args: _*)(curNode.typeTag)),
                    ),
                    curModWithPreds.init,
                )
                /* update the variable for this node
                    e.g. newNext ==
                          /\ oldNext
                          /\ curNode_predicate' = A_predicate' /\ B_predicate'
                 */
                val newNext = conjunctExToOperDecl(
                    OperEx(oper, argExs: _*)(curNode.typeTag),
                    curModWithPreds.next,
                )

                curModWithPreds = curModWithPreds.setPredicates(newInit, newNext, curModWithPreds.loopOK)

                (
                    curModWithPreds,
                    /* expression for this node is the name of the variable that encodes it */
                    builder.declAsNameEx(nodeVarDecl),
                )
            }
        }
      case _ => /* a propositional expression - used as-is in the formula encoding the syntax tree */
        (modWithPreds, curNode)
    }
  }

}

object TableauEncoder {
  val NAME_PREFIX = ""
}
