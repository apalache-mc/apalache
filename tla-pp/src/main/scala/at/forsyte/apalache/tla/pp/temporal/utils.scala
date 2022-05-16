package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import scalaz.Scalaz._

object ScopedBuilderExtensions {
  implicit class ScopedBuilderExtension(val builder: ScopedBuilder) {
    def primeVar(varDecl: TlaVarDecl): TBuilderInstruction = {
      prime(declAsNameEx(varDecl))
    }

    def prime(expression: TlaEx): TBuilderInstruction = {
      createUnsafeInstruction(OperEx(TlaActionOper.prime, expression)(expression.typeTag))
    }

    def declAsNameEx(varDecl: TlaVarDecl): TBuilderInstruction = {
      builder.name(varDecl.name, varDecl.typeTag.asTlaType1())
    }

    def createUnsafeInstruction[T <: TlaEx](ex: T): TBuilderInstruction = {
      ex.asInstanceOf[TlaEx].point[TBuilderInternalState]
    }
  }
}

class ModWithPreds(
    val module: TlaModule,
    val init: TlaOperDecl,
    val next: TlaOperDecl,
    val loopOK: TlaOperDecl) {

  def setPredicates(newInit: TlaOperDecl, newNext: TlaOperDecl, newLoopOK: TlaOperDecl): ModWithPreds = {
    val newDeclarations = module.declarations.map(decl =>
      decl.name match {
        case init.name   => newInit
        case next.name   => newNext
        case loopOK.name => newLoopOK
        case _           => decl
      })
    val newModule = new TlaModule(module.name, newDeclarations)
    new ModWithPreds(newModule, newInit, newNext, newLoopOK)
  }
}

package object utils {
  val builder: ScopedBuilder = new ScopedBuilder()
}

object DeclUtils {
  import at.forsyte.apalache.tla.pp.temporal.ScopedBuilderExtensions._
  import at.forsyte.apalache.tla.pp.temporal.utils.builder

  /**
   * Takes decl, ex and returns newDecl with the same name as decl, with its body extended like this: newDecl == decl /\
   * ex
   */
  def conjunctExToOperDecl(ex: TlaEx, decl: TlaOperDecl): TlaOperDecl = {
    new TlaOperDecl(
        decl.name,
        decl.formalParams,
        builder.and(
            builder.createUnsafeInstruction(decl.body),
            builder.createUnsafeInstruction(ex),
        ),
    )(Typed(BoolT1))
  }
}
