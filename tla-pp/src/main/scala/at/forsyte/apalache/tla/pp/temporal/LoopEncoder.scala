package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.pp.temporal.ScopedBuilderExtensions._
import at.forsyte.apalache.tla.pp.temporal.DeclUtils._
import at.forsyte.apalache.tla.pp.temporal.utils.builder
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

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
class LoopEncoder(gen: UniqueNameGenerator) extends LazyLogging {
  import LoopEncoder.NAME_PREFIX

  val boolTag = Typed(BoolT1)

  val inLoopDecl = TlaVarDecl(s"${NAME_PREFIX}InLoop_${gen.newName()}")(boolTag)
  val inLoop = builder.declAsNameEx(inLoopDecl)
  val inLoopPrime = builder.primeVar(inLoopDecl)

  /** For each variable foo, creates a declaration of an auxiliary variable loop_foo */
  def createLoopVariables(originalVariables: Seq[TlaVarDecl]): Seq[TlaVarDecl] = {
    originalVariables.map(varDecl => createLoopVariableForVariable(varDecl))
  }

  def createLoopVariableForVariable(varDecl: TlaVarDecl): TlaVarDecl = {
    TlaVarDecl(s"${NAME_PREFIX}Loop_${varDecl.name}_${gen.newName()}")(varDecl.typeTag)
  }

  /**
   * Takes a variable foo and its corresponding loop variable loop_foo, and transforms init into
   *
   * newInit == init /\ loop_foo = foo
   */
  def addLoopVarToInit(varDecl: TlaVarDecl, loopVarDecl: TlaVarDecl, init: TlaOperDecl): TlaOperDecl = {
    conjunctExToOperDecl(
        builder.eql(builder.declAsNameEx(loopVarDecl), builder.declAsNameEx(varDecl)),
        init,
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
   * /\ loop_foo = foo
   *
   * /\ loop_bar = bar
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
        /\ loop_foo = foo
        /\ loop_bar = bar
        /\ ...
     */
    conjunctExToOperDecl(inLoopEqlFalse, initWithLoopVarInits)
  }

  /**
   * Adds logic for manipulating the loop_var in next. Transforms next into
   *
   * newNext ==
   *
   * /\ oldNext
   *
   * /\ loop_foo' = IF (InLoop' = InLoop) THEN loop_foo ELSE foo
   */
  def addLoopVarToNext(varDecl: TlaVarDecl, loopVarDecl: TlaVarDecl, next: TlaOperDecl): TlaOperDecl = {
    val loopEx = builder.declAsNameEx(varDecl)
    val loopExPrime = builder.prime(loopEx)

    TlaOperDecl(
        next.name,
        next.formalParams,
        builder.and(
            /* oldNext */
            builder.createUnsafeInstruction(next.body),
            /* loop_foo' \in {loop_foo, foo} */
            builder.in(builder.primeVar(loopVarDecl),
                builder.enumSet(builder.declAsNameEx(varDecl), builder.declAsNameEx(loopVarDecl))),
            /* /\ loop_foo' = IF (InLoop' = InLoop) THEN loop_foo ELSE foo */
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

    val nextOrUnchangedWithInLoopUpdate = conjunctExToOperDecl(inLoopUpdate, next)

    /*
     * /\ loop_foo' = IF (InLoop' = InLoop) THEN loop_foo ELSE foo
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
   * /\ foo = loop_foo
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

  /**
   * Creates a loopOK predicate over the provided variables.
   *
   * loopOK ==
   *
   * /\ InLoop
   *
   * /\ foo = loop_foo
   *
   * /\ bar = loop_bar
   */
  def createLoopOKPredicate(
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl]): TlaOperDecl = {

    /* loopOK == InLoop */
    val loopOK =
      new TlaOperDecl(
          s"${NAME_PREFIX}LoopOK_${gen.newName()}",
          List(),
          inLoop,
      )(Typed(OperT1(Seq.empty, BoolT1)))

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

  /**
   * A prefix added to the names of all variables used for the loop encoding. Useful for disambiguating them from
   * variables in the original spec, particularly if those mention loops as well.
   */
  val NAME_PREFIX = "__copy_"
}
