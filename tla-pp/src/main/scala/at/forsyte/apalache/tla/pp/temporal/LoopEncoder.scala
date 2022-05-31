package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.pp.temporal.ScopedBuilderExtensions._
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
  val inLoop = builder.declAsNameEx(inLoopDecl)
  val inLoopPrime = builder.primeVar(inLoopDecl)

  /**
   * For each variable foo, creates a declaration of an auxiliary variable __saved_foo __saved_foo stores the value of
   * variable foo at the start of the loop.
   */
  def createAllVarCopiesInLoop(originalVariables: Seq[TlaVarDecl]): Seq[TlaVarDecl] = {
    originalVariables.map(varDecl => createVarCopyVariableInLoop(varDecl))
  }

  def createVarCopyVariableInLoop(varDecl: TlaVarDecl): TlaVarDecl = {
    TlaVarDecl(s"${NAME_PREFIX}${varDecl.name}")(varDecl.typeTag)
  }

  /**
   * Takes a variable foo and its corresponding save variable __saved_foo, and transforms init into
   *
   * newInit == init /\ __saved_foo = foo
   */
  def addLoopVarToInit(varDecl: TlaVarDecl, loopVarDecl: TlaVarDecl, init: TlaOperDecl): TlaOperDecl = {
    andInDecl(
        builder.eql(builder.declAsNameEx(loopVarDecl), builder.declAsNameEx(varDecl)),
        init,
        tracker,
    )
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

    val initWithLoopVarInits =
      variables
        .zip(loopVariables)
        .foldLeft(init)({ case (curInit, (varDecl, loopVarDecl)) =>
          addLoopVarToInit(varDecl, loopVarDecl, curInit)
        })

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
    andInDecl(inLoopEqlFalse, initWithLoopVarInits, tracker)
  }

  /**
   * Adds logic for manipulating the loop_var in next. Transforms next into
   *
   * newNext ==
   *
   * /\ oldNext
   *
   * /\ __saved_foo' = IF (InLoop' = InLoop) THEN loop_foo ELSE foo
   */
  def addLoopVarToNext(varDecl: TlaVarDecl, loopVarDecl: TlaVarDecl, next: TlaOperDecl): TlaOperDecl = {
    val loopEx = builder.declAsNameEx(loopVarDecl)
    val loopExPrime = builder.prime(loopEx)

    TlaOperDecl(
        next.name,
        next.formalParams,
        builder.and(
            /* oldNext */
            builder.useTrustedEx(next.body),
            /* /\ __saved_foo' = IF (InLoop' = InLoop) THEN __saved_foo ELSE foo */
            builder.eql(
                loopExPrime,
                builder.ite(
                    builder.eql(inLoop, inLoopPrime),
                    loopEx,
                    builder.declAsNameEx(varDecl),
                ),
            ),
        ),
    )(next.typeTag)
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
     * /\ __saved_foo' = IF (InLoop' = InLoop) THEN __saved_foo ELSE foo
     */
    variables.zip(loopVariables).foldLeft(nextOrUnchangedWithInLoopUpdate) { case (curNext, (varDecl, loopVarDecl)) =>
      addLoopVarToNext(varDecl, loopVarDecl, curNext)
    }
  }

  /**
   * Adds a loop variable to the loopOK expression by transforming loopOK into
   *
   * newLoopOK ==
   *
   * /\ oldLoopOK
   *
   * /\ foo = __saved_foo
   */
  def addVariableToLoopOK(
      varDecl: TlaVarDecl,
      loopVarDecl: TlaVarDecl,
      loopOK: TlaOperDecl): TlaOperDecl = {

    andInDecl(
        builder.eql(builder.declAsNameEx(varDecl), builder.declAsNameEx(loopVarDecl)),
        loopOK,
        tracker,
    )
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

    /* loopOK == InLoop */
    val loopOK =
      new TlaOperDecl(
          LoopEncoder.LOOP_OK_NAME,
          List(),
          inLoop,
      )(Typed(OperT1(Seq.empty, BoolT1)))

    /* loopOK ==
        /\ InLoop
        /\ foo = __saved_foo
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
    )(loopOK.typeTag)
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
  val IN_LOOP_NAME = s"${NAME_PREFIX}InLoop"
  val LOOP_OK_NAME = s"${NAME_PREFIX}LoopOK"
}
