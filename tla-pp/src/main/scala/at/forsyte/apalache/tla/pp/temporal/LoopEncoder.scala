package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.pp.temporal.ScopedBuilderExtensions._
import at.forsyte.apalache.tla.pp.temporal.DeclUtils._
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

/**
 * Encode temporal operators.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class LoopEncoder(gen: UniqueNameGenerator) extends LazyLogging {
  import LoopEncoder.NAME_PREFIX

  implicit val typeTag: TypeTag = Typed(BoolT1())
  val inLoopDecl = TlaVarDecl(s"${NAME_PREFIX}InLoop_${gen.newName()}")
  val inLoop = builder.declAsNameEx(inLoopDecl)
  val inLoopPrime = builder.primeVar(inLoopDecl)


  def createLoopVariables(originalVariables: Seq[TlaVarDecl]): Seq[TlaVarDecl] = {
    originalVariables.map(varDecl => createLoopVariableForVariable(varDecl))
  }

  def createLoopVariableForVariable(varDecl: TlaVarDecl): TlaVarDecl = {
    TlaVarDecl(s"${NAME_PREFIX}Loop_${varDecl.name}_${gen.newName()}")(varDecl.typeTag)
  }

  /**
   * Transforms init into newInit == init /\ loop_foo = foo
   */
  def addLoopVarToInit(varDecl: TlaVarDecl, loopVarDecl: TlaVarDecl, init: TlaOperDecl): TlaOperDecl = {
    conjunctExToOperDecl(
        builder.eql(builder.declAsNameEx(loopVarDecl), builder.declAsNameEx(varDecl)),
        init,
    )
  }

  /**
   * Transforms init into /\ init /\ InLoop <=> FALSE /\ loop_foo = foo /\ loop_bar = bar ...
   */
  def addLoopLogicToInit(
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      init: TlaOperDecl): TlaOperDecl = {

    val initWithLoopVarInits =
      variables
        .zip(loopVariables)
        .foldLeft(init)({ case (curInit, (varDecl, loopVarDecl)) =>
          addLoopVarToInit(varDecl, loopVarDecl, curInit)
        })

    //  ~inLoop
    val inLoopEquivFalse =
      builder.not(inLoop)

    /*
        /\ ~inLoop
        /\ init
        /\ loop_foo = foo
        /\ loop_bar = bar
        /\ ...
     */
    conjunctExToOperDecl(inLoopEquivFalse, initWithLoopVarInits)
  }

  /* Transforms next into
      newNext ==
        /\ oldNext
        /\ loop_foo' \in {loop_foo, foo}
        /\ InLoop' \= InLoop => loop_foo' = foo
        /\ InLoop' = InLoop => loop_foo' = loop_foo
   */
  def addLoopVarToNext(varDecl: TlaVarDecl, loopVarDecl: TlaVarDecl, next: TlaOperDecl): TlaOperDecl = {
    TlaOperDecl(
        next.name,
        next.formalParams,
        builder.and(
            /* oldNext */
            builder.createUnsafeInstruction(next.body),
            /* loop_foo' \in {loop_foo, foo} */
            builder.in(builder.primeVar(loopVarDecl),
                builder.enumSet(builder.declAsNameEx(varDecl), builder.declAsNameEx(loopVarDecl))),
            /* InLoop' \= InLoop => loop_foo' = foo */
            builder.impl(
                builder.neql(inLoopPrime, inLoop),
                builder.eql(builder.primeVar(loopVarDecl), builder.declAsNameEx(varDecl)),
            ),
            /* InLoop' = InLoop => loop_foo' = loop_foo */
            builder.impl(
                builder.eql(inLoopPrime, inLoop),
                builder.eql(builder.primeVar(loopVarDecl), builder.declAsNameEx(loopVarDecl)),
            ),
        ),
    )
  }

  def addLoopLogicToNext(
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      next: TlaOperDecl): TlaOperDecl = {
    implicit val typeTag: TypeTag = Typed(BoolT1())

    val varsUnchanged =
      builder.and(variables.map { varDecl =>
        builder.createUnsafeInstruction(OperEx(TlaActionOper.unchanged, builder.declAsNameEx(varDecl))(typeTag))
      }: _*)

    /*
     * next \/ /\ UNCHANGED foo
     *         /\ UNCHANGED bar
     *         ...
     */
    val nextOrUnchanged =
      new TlaOperDecl(
          next.name,
          next.formalParams,
          builder.or(builder.createUnsafeInstruction(next.body), varsUnchanged),
      )

    /*
     * /\  /\ loop_foo' \in {loop_foo, foo}
     *     /\ InLoop' \= InLoop => loop_foo' = foo
     *     /\ InLoop' = InLoop => loop_foo' = loop_foo
     * /\  /\ loop_bar' \in {loop_bar, bar}
     *     /\ InLoop' \= InLoop => loop_bar' = bar
     *     /\ InLoop' = InLoop => loop_bar' = loop_bar
     */
    val nextWithLoopVarUpdates =
      variables.zip(loopVariables).foldLeft(nextOrUnchanged) { case (curNext, (varDecl, loopVarDecl)) =>
        addLoopVarToNext(varDecl, loopVarDecl, curNext)
      }

    /*
     * /\ InLoop' \in {TRUE, FALSE}
     * /\ InLoop => InLoop'
     */
    val inLoopUpdate =
      builder.and(
          builder.in(inLoopPrime, builder.booleanSet()),
          builder.impl(inLoop, inLoopPrime),
      )

    conjunctExToOperDecl(inLoopUpdate, nextWithLoopVarUpdates)
  }

  /*
    Transforms loopOK into
      newLoopOK ==
        /\ oldLoopOK
        /\ foo = loop_foo
   */
  def addVariableToLoopOK(
      varDecl: TlaVarDecl,
      loopVarDecl: TlaVarDecl,
      loopOK: TlaOperDecl): TlaOperDecl = {

    conjunctExToOperDecl(
        builder.eql(builder.declAsNameEx(varDecl), builder.declAsNameEx(loopVarDecl)),
        loopOK,
    )
  }

  def createLoopOKPredicate(
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl]): TlaOperDecl = {

    /* loopOK == InLoop */
    val loopOK = new TlaOperDecl(s"${NAME_PREFIX}LoopOK_${gen.newName()}", List(), inLoop)

    /* loopOK ==
        /\ InLoop
        /\ foo = loop_foo
        /\ ...
     */
    val loopVarEqualities = variables.zip(loopVariables).foldLeft(loopOK) {
      case (
              curLoopOK,
              (varDecl, loopVarDecl),
          ) =>
        addVariableToLoopOK(varDecl, loopVarDecl, curLoopOK)
    }

    new TlaOperDecl(
        loopOK.name,
        loopOK.formalParams,
        loopVarEqualities.body,
    )
  }

  /**
   * @returns:
   *   A tuple containing the new module, the new init predicate, the new next predicate, and the new LoopOK predicate
   */
  def addLoopLogic(
      module: TlaModule,
      init: TlaOperDecl,
      next: TlaOperDecl): ModWithPreds = {
    val variables = module.varDeclarations
    val loopVariables = createLoopVariables(variables)

    val newInit = addLoopLogicToInit(variables, loopVariables, init)

    val newNext = addLoopLogicToNext(variables, loopVariables, next)

    val loopOk = createLoopOKPredicate(variables, loopVariables)

    val newDeclarations = module.declarations.map(decl =>
      decl.name match {
        case init.name => newInit
        case next.name => newNext
        case _         => decl
      })

    new ModWithPreds(new TlaModule(module.name, (loopVariables :+ inLoopDecl) ++ (newDeclarations :+ loopOk)), newInit,
        newNext, loopOk)
  }
}

object LoopEncoder {
  val NAME_PREFIX = ""
}
