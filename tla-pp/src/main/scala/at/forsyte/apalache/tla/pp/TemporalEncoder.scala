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

/**
 * Encode temporal operators.
 *
 * @author
 *   Philip Offtermatt
 */
@Singleton
class TemporalEncoder(module: TlaModule, gen: UniqueNameGenerator) extends LazyLogging {
  import TemporalEncoder.NAME_PREFIX
  val levelFinder = new TlaLevelFinder(module)

  implicit val typeTag: TypeTag = Typed(BoolT1())

  def encodeInvariants(invariants: List[String], init: String, next: String): TlaModule = {
    val temporalInvariants = invariants.filter(invName => {
      module.declarations.find(_.name == invName) match {
        case Some(inv: TlaOperDecl) if inv.formalParams.isEmpty =>
          // either a state invariant, or an action invariant
          val level = levelFinder.getLevelOfDecl(inv)
          level == TlaLevelTemporal
        case _ => false
      }
    })

    if (temporalInvariants.isEmpty) {
      logger.info("  > No temporal properties found, nothing to encode")
      module
    } else {
      logger.info(s"  > Found ${temporalInvariants.length} temporal invariants")
      logger.info(s"  > Adding logic for loop finding")

      val initDecl = module.declarations.find(_.name == init) match {
        case Some(initDecl: TlaOperDecl) =>
          val nparams = initDecl.formalParams.length
          if (nparams != 0) {
            val message =
              s"Expected init predicate $init to have 0 params, found $nparams parameters"
            throw new TlaInputError(message, Some(initDecl.body.ID))
          }
          initDecl
        case None =>
          val message = (s"init predicate named `${init}` not found")
          throw new TlaInputError(message)
        case _ =>
          val message = (s"Expected to find a predicate named `${init}` but did not")
          throw new TlaInputError(message)
      }

      val nextDecl = module.declarations.find(_.name == next) match {
        case Some(nextDecl: TlaOperDecl) =>
          val nparams = nextDecl.formalParams.length
          if (nparams != 0) {
            val message =
              s"Expected next predicate $init to have 0 params, found $nparams parameters"
            throw new TlaInputError(message, Some(nextDecl.body.ID))
          }
          nextDecl
        case None =>
          val message = (s"next predicate named `${init}` not found")
          throw new TlaInputError(message)
        case _ =>
          val message = (s"Expected to find a predicate named `${init}` but did not")
          throw new TlaInputError(message)
      }

      val moduleWithLoopLogic = addLoopLogic(module, initDecl, nextDecl)
      moduleWithLoopLogic
    }
  }

  def createLoopVariables(originalVariables: Seq[TlaVarDecl]): Seq[TlaVarDecl] = {
    originalVariables.map(varDecl => createLoopVariableForVariable(varDecl))
  }

  def createLoopVariableForVariable(varDecl: TlaVarDecl): TlaVarDecl = {
    TlaVarDecl(s"${NAME_PREFIX}Loop_${varDecl.name}_${gen.newName()}")(varDecl.typeTag)
  }

  def addLoopLogicToInit(
      inLoop: TlaVarDecl,
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      init: TlaOperDecl): TlaDecl = {

    //  inLoop <=> FALSE
    val inLoopInitBody =
      OperEx(TlaBoolOper.equiv, NameEx(inLoop.name), new ValEx(new TlaBool(false)))

    val varsWithLoopDuplicates =
      variables.zip(loopVariables)

    val equivalences =
      varsWithLoopDuplicates.map { case (varDecl, loopVarDecl) =>
        OperEx(TlaOper.eq, NameEx(varDecl.name)(varDecl.typeTag), NameEx(loopVarDecl.name)(loopVarDecl.typeTag))
      }

    /*
        /\ loop_foo = foo
        /\ loop_bar = bar
        /\ ...
     */
    val loopEquivalencesBody = OperEx(TlaBoolOper.and, equivalences: _*)

    /*  /\ init
        /\ inLoop <=> FALSE
        /\ loop_foo = foo
        /\ loop_bar = bar
        /\ ...
     */
    val loopInitBody = OperEx(TlaBoolOper.and, init.body, inLoopInitBody, loopEquivalencesBody)

    new TlaOperDecl(init.name, init.formalParams, loopInitBody)(init.typeTag)
  }

  def ImpliesEq(condition: TlaEx, op1: TlaEx, op2: TlaEx): TlaEx = {
    OperEx(TlaBoolOper.implies, condition, OperEx(TlaOper.eq, op1, op2))
  }

  def PrimeVar(varDecl: TlaVarDecl): TlaEx = {
    Prime(NameEx(varDecl.name)(varDecl.typeTag))
  }

  def Prime(expression: TlaEx): TlaEx = {
    OperEx(TlaActionOper.prime, expression)(expression.typeTag)
  }

  def VarName(varDecl: TlaVarDecl): TlaEx = {
    NameEx(varDecl.name)(varDecl.typeTag)
  }

  def addLoopLogicToNext(
      inLoop: TlaVarDecl,
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl],
      next: TlaOperDecl): TlaDecl = {
    implicit val typeTag: TypeTag = Typed(BoolT1())

    val unchanged =
      OperEx(TlaBoolOper.and,
          variables.map { varDecl =>
            OperEx(TlaActionOper.unchanged, VarName(varDecl))(Untyped())
          }: _*)
    val nextBodyOrUnchanged = OperEx(TlaBoolOper.or, next.body, unchanged)

    val variablesLoopUpdate =
      variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
        val varTypeTag = varDecl.typeTag
        val varTypeT1 = TlaType1.fromTypeTag(varTypeTag)
        // loop_foo' \in {foo, loop_foo}
        OperEx(TlaBoolOper.and,
            OperEx(TlaSetOper.in, PrimeVar(loopVarDecl),
                OperEx(TlaSetOper.enumSet, VarName(varDecl), VarName(loopVarDecl))(Typed(SetT1(varTypeT1)))),
            ImpliesEq(OperEx(TlaOper.ne, PrimeVar(inLoop), VarName(inLoop)), PrimeVar(loopVarDecl),
                VarName(varDecl)),
            ImpliesEq(OperEx(TlaOper.eq, PrimeVar(inLoop), VarName(inLoop)), PrimeVar(loopVarDecl),
                VarName(loopVarDecl)))
      }

    val variablesLoopNextBody =
      OperEx(TlaBoolOper.and, variablesLoopUpdate: _*)

    val loopNextBody = OperEx(TlaBoolOper.and,
        OperEx(TlaSetOper.in, NameEx(inLoop.name),
            OperEx(TlaSetOper.enumSet, ValEx(TlaBool(false)), ValEx(TlaBool(true)))(Typed(SetT1(BoolT1())))), variablesLoopNextBody)

    new TlaOperDecl(next.name, next.formalParams, OperEx(TlaBoolOper.and, nextBodyOrUnchanged, loopNextBody))
  }

  def createLoopOkPredicate(
      inLoop: TlaVarDecl,
      variables: Seq[TlaVarDecl],
      loopVariables: Seq[TlaVarDecl]): TlaOperDecl = {
    val loopVarEqualities = variables.zip(loopVariables).map { case (varDecl, loopVarDecl) =>
      OperEx(TlaOper.eq, NameEx(varDecl.name), NameEx(loopVarDecl.name))
    }

    val loopVarsOk = OperEx(TlaBoolOper.and, loopVarEqualities: _*)

    new TlaOperDecl(s"${NAME_PREFIX}LoopOK_${gen.newName()}", List(),
        OperEx(TlaBoolOper.and, NameEx(inLoop.name), loopVarsOk))
  }

  def addLoopLogic(module: TlaModule, init: TlaOperDecl, next: TlaOperDecl): TlaModule = {
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

    new TlaModule(module.name, (loopVariables :+ inLoop) ++ (newDeclarations :+ loopOk))
  }
}

object TemporalEncoder {
  val NAME_PREFIX = ""
}
