package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.tla.lir._

import javax.inject.Singleton
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.oper.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.values.TlaPredefSet
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.typecomp._
import scalaz._
import scalaz.Scalaz._

/**
 * Encode temporal operators.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class LoopEncoder(gen: UniqueNameGenerator) extends LazyLogging {
  import LoopEncoder.NAME_PREFIX
  val builder = new ScopedBuilder()

  implicit val typeTag: TypeTag = Typed(BoolT1())

  def createLoopVariables(originalVariables: Seq[TlaVarDecl]): Seq[TlaVarDecl] = {
    originalVariables.map(varDecl => createLoopVariableForVariable(varDecl))
  }

  def createLoopVariableForVariable(varDecl: TlaVarDecl): TlaVarDecl = {
    TlaVarDecl(s"${NAME_PREFIX}Loop_${varDecl.name}_${gen.newName()}")(varDecl.typeTag)
  }

  def PrimeVar(varDecl: TlaVarDecl): TBuilderInstruction = {
    Prime(DeclAsNameEx(varDecl))
  }

  def Prime(expression: TlaEx): TBuilderInstruction = {
    CreateUnsafeInstruction(OperEx(TlaActionOper.prime, expression)(expression.typeTag))
  }

  def DeclAsNameEx(varDecl: TlaVarDecl): TBuilderInstruction = {
    builder.name(varDecl.name, varDecl.typeTag.asTlaType1())
  }

  def CreateUnsafeInstruction[T <: TlaEx](ex: T): TBuilderInstruction = {
    ex.asInstanceOf[TlaEx].point[TBuilderInternalState]
  }

  /**
   * Transforms init into /\ init /\ InLoop <=> FALSE /\ loop_foo = foo /\ loop_bar = bar ...
   */
  def addLoopLogicToInit(
      inLoop: TlaVarDecl,
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      init: TlaOperDecl): TlaOperDecl = {

    //  ~inLoop
    val inLoopEquivFalse =
      builder.not(DeclAsNameEx(inLoop))

    val varsEqLoopVars =
      variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
        builder.eql(DeclAsNameEx(loopVarDecl), DeclAsNameEx(varDecl))
      }

    /*
        /\ loop_foo = foo
        /\ loop_bar = bar
        /\ ...
     */
    val varsEqLoopVarsConjunction = builder.and(varsEqLoopVars: _*)

    /*  /\ init
        /\ inLoop <=> FALSE
        /\ loop_foo = foo
        /\ loop_bar = bar
        /\ ...
     */
    val loopInitBody = builder.and(CreateUnsafeInstruction(init.body), inLoopEquivFalse, varsEqLoopVarsConjunction)

    new TlaOperDecl(init.name, init.formalParams, loopInitBody)(init.typeTag)
  }

  def addLoopLogicToNext(
      inLoopDecl: TlaVarDecl,
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      next: TlaOperDecl): TlaOperDecl = {
    implicit val typeTag: TypeTag = Typed(BoolT1())

    val inLoop = DeclAsNameEx(inLoopDecl)
    val inLoopPrime = PrimeVar(inLoopDecl)

    val varsUnchanged =
      builder.and(variables.map { varDecl =>
        CreateUnsafeInstruction(OperEx(TlaActionOper.unchanged, DeclAsNameEx(varDecl))(typeTag))
      }: _*)

    /*
     * next \/ /\ UNCHANGED foo
     *         /\ UNCHANGED bar
     *         ...
     */
    val nextOrUnchanged = builder.or(CreateUnsafeInstruction(next.body), varsUnchanged)

    /*
     * /\  /\ loop_foo' \in {loop_foo, foo}
     *     /\ InLoop' \= InLoop => loop_foo' = foo
     *     /\ InLoop' = InLoop => loop_foo' = loop_foo
     * /\  /\ loop_bar' \in {loop_bar, bar}
     *     /\ InLoop' \= InLoop => loop_bar' = bar
     *     /\ InLoop' = InLoop => loop_bar' = loop_bar
     */
    val varsLoopUpdate =
      variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
        // loop_foo' \in {foo, loop_foo}
        builder.and(
            builder.in(inLoopPrime, builder.enumSet(DeclAsNameEx(varDecl), DeclAsNameEx(loopVarDecl))),
            builder.impl(
                builder.neql(inLoopPrime, inLoop),
                builder.eql(inLoopPrime, DeclAsNameEx(varDecl)),
            ),
            builder.impl(
                builder.eql(inLoopPrime, inLoop),
                builder.eql(inLoopPrime, DeclAsNameEx(loopVarDecl)),
            ),
        )
      }
    val varsLoopUpdateConjunction =
      builder.and(varsLoopUpdate: _*)

    /*
     * /\ InLoop' \in {TRUE, FALSE}
     * /\ InLoop => InLoop'
     */
    val inLoopUpdate =
      builder.and(
          builder.in(inLoopPrime, builder.booleanSet()),
          builder.impl(inLoop, inLoopPrime),
      )

    val loopNextBody = builder.and(inLoopUpdate, varsLoopUpdateConjunction)

    new TlaOperDecl(next.name, next.formalParams, builder.and(nextOrUnchanged, loopNextBody))(next.typeTag)
  }

  def createLoopOkPredicate(
      inLoopDecl: TlaVarDecl,
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl]): TlaOperDecl = {

    val inLoop = DeclAsNameEx(inLoopDecl)

    val loopVarEqualities = variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
      builder.eql(DeclAsNameEx(varDecl), DeclAsNameEx(loopVarDecl))
    }

    val loopVarsOk = builder.and(loopVarEqualities: _*)

    new TlaOperDecl(s"${NAME_PREFIX}LoopOK_${gen.newName()}", List(), builder.and(inLoop, loopVarsOk))
  }

  /**
   * @returns:
   *   A tuple containing the new module, the new init predicate, the new next predicate, and the new LoopOK predicate
   */
  def addLoopLogic(
      module: TlaModule,
      init: TlaOperDecl,
      next: TlaOperDecl): (TlaModule, TlaOperDecl, TlaOperDecl, TlaOperDecl) = {
    val inLoop = TlaVarDecl(s"${NAME_PREFIX}InLoop_${gen.newName()}")
    val variables = module.varDeclarations
    val loopVariables = createLoopVariables(variables)

    val newInit = addLoopLogicToInit(inLoop, variables, loopVariables, init)

    val newNext = addLoopLogicToNext(inLoop, variables, loopVariables, next)

    val loopOk = createLoopOkPredicate(inLoop, variables, loopVariables)

    val newDeclarations = module.declarations.map(decl =>
      decl.name match {
        case init.name => newInit
        case next.name => newNext
        case _         => decl
      })

    (new TlaModule(module.name, (loopVariables :+ inLoop) ++ (newDeclarations :+ loopOk)), newInit, newNext, loopOk)
  }
}

object LoopEncoder {
  val NAME_PREFIX = ""
}
