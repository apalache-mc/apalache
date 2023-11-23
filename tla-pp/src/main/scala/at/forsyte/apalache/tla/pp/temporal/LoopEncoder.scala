package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._

import com.google.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.pp.temporal.DeclUtils._
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker

/**
 * A class for adding loop logic to a TLA Module: An extra variable InLoop is added, which, in each step, can
 * nondeterministically be set to true. When the variable is set to true, the current values of variables are stored in
 * copies of the variables (e.g. the value of foo is stored in an auxiliary variable loop_foo). When InLoop is true, the
 * system is inside of the loop.
 *
 * It is ensured that the execution loops, i.e. the state at the start of the loop is the same as the state at the end
 * of the execution, by considering only traces where the variable values at the last state match the ones that were
 * stored at the start of the loop.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class LoopEncoder(tracker: TransformationTracker) extends LazyLogging {
  import LoopEncoder.NAME_PREFIX

  val boolTag = Typed(BoolT1)

  val inLoopDecl = TlaVarDecl(LoopEncoder.IN_LOOP_NAME)(boolTag)
  val inLoop = builder.varDeclAsNameEx(inLoopDecl)
  val inLoopPrime = builder.prime(inLoop)

  /**
   * For each variable foo, creates a declaration of an auxiliary variable __saved_foo which stores the value of
   * variable foo at the start of the loop.
   */
  def createAllVarCopiesInLoop(originalVariables: Seq[TlaVarDecl]): Seq[TlaVarDecl] = {
    originalVariables.map(varDecl => createVarCopyVariableInLoop(varDecl))
  }

  def createVarCopyVariableInLoop(varDecl: TlaVarDecl): TlaVarDecl = {
    TlaVarDecl(s"${NAME_PREFIX}${varDecl.name}")(varDecl.typeTag)
  }

  /**
   * Transforms init into
   *
   * newInit ==
   *
   * /\ init
   *
   * /\ inLoop = FALSE
   *
   * /\ __saved_foo = foo
   *
   * /\ __saved_bar = bar
   *
   * ...
   */
  def addLoopLogicToInit(
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      init: TlaOperDecl): TlaOperDecl = {

    /*
      __saved_foo = foo, __saved_bar = bar
     */
    val eqls =
      variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
        builder.eql(builder.varDeclAsNameEx(loopVarDecl), builder.varDeclAsNameEx(varDecl))
      }

    //  inLoop = FALSE
    val inLoopEqlFalse =
      builder.eql(inLoop, builder.bool(false))

    /*
        /\ inLoop = FALSE
        /\ init
        /\ __saved_foo = foo
        /\ __saved_bar = bar
        /\ ...
     */
    andInDecl(
        builder.and(inLoopEqlFalse +: eqls: _*),
        init,
        tracker,
    )
  }

  /**
   * Returns an expression for updating the loop_var
   *
   * {{{__saved_foo' = IF (InLoop' = InLoop) THEN loop_foo ELSE foo}}}
   */
  def getLoopVarUpdateEx(varEx: TBuilderInstruction, loopVarEx: TBuilderInstruction): TBuilderInstruction = {
    builder.eql(
        builder.prime(loopVarEx),
        builder.ite(
            builder.eql(inLoop, inLoopPrime),
            loopVarEx,
            varEx,
        ),
    )
  }

  /**
   * Modifies next to include the logic for updating InLoop and the loop variables.
   */
  def addLoopLogicToNext(
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      next: TlaOperDecl): TlaOperDecl = {

    /*
     * /\ InLoop' \in {TRUE, FALSE}
     * /\ InLoop => InLoop'
     */
    val inLoopUpdate =
      builder.and(
          builder.in(inLoopPrime, builder.booleanSet()),
          builder.impl(inLoop, inLoopPrime),
      )

    val nextOrUnchangedWithInLoopUpdate = andInDecl(inLoopUpdate, next, tracker)

    /*
     * __saved_foo' := foo, __saved_bar' := bar, ..., __saved_baz' := baz
     */
    val eqls = variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
      val loopExPrime = builder.prime(builder.varDeclAsNameEx(loopVarDecl))
      /* /\ __saved_foo' = IF (InLoop' = InLoop) THEN __saved_foo ELSE foo */
      builder.eql(
          loopExPrime,
          builder.varDeclAsNameEx(varDecl),
      )
    }

    /**
     * IF (InLoop' = InLoop)
     *
     * THEN UNCHANGED <<__saved_foo, __saved_bar, ..., __saved_baz>>
     *
     * ELSE
     *
     * /\ __saved_foo' := foo
     *
     * /\ __saved_bar' := bar
     *
     * ...
     *
     * /\ __saved_baz' := baz
     */
    val ite = builder.ite(
        builder.eql(inLoop, inLoopPrime),
        builder.unchanged(
            builder.tuple(loopVariables.map(varDecl => builder.varDeclAsNameEx(varDecl)): _*)
        ),
        builder.and(eqls: _*),
    )

    andInDecl(ite, nextOrUnchangedWithInLoopUpdate, tracker)
  }

  /**
   * Creates a loopOK predicate over the provided variables. LoopOK answers the question "Does the execution right now
   * encode a proper loop?" So it ensures that a) the loop has been started and b) the saved copies of the variables
   * have the same value as the variables right now, e.g. the loop is closed
   *
   * loopOK ==
   *
   * /\ InLoop
   *
   * /\ foo = __saved_foo
   *
   * /\ bar = __saved_foo
   */
  def createLoopOKPredicate(
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl]): TlaOperDecl = {

    /* loopOK ==
        /\ InLoop
        /\ foo = __saved_foo
        /\ ...
     */
    val eqls = variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
      builder.eql(builder.varDeclAsNameEx(varDecl), builder.varDeclAsNameEx(loopVarDecl))
    }
    builder.decl(
        LoopEncoder.LOOP_OK_NAME,
        builder.and(inLoop +: eqls: _*),
    )
  }

  /**
   * Adds loop logic to the module.
   *
   * @see
   *   [[addLoopLogicToNext]]
   * @see
   *   [[addLoopLogicToInit]]
   * @see
   *   [[createLoopOKPredicate]]
   */
  def addLoopLogic(
      module: TlaModule,
      init: TlaOperDecl,
      next: TlaOperDecl): ModWithPreds = {
    val variables = module.varDeclarations
    val loopVariables = createAllVarCopiesInLoop(variables)

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

  /**
   * A prefix added to the names of all variables used for the loop encoding. Useful for disambiguating them from
   * variables in the original spec.
   */
  val NAME_PREFIX = "__saved_"
  val IN_LOOP_NAME = s"__InLoop"
  val LOOP_OK_NAME = s"__LoopOK"
}
