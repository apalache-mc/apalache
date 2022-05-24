package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import scalaz.Scalaz._
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.Flatten

object ScopedBuilderExtensions {
  implicit class ScopedBuilderExtension(val builder: ScopedBuilder) {
    def primeVar(varDecl: TlaVarDecl): TBuilderInstruction = {
      prime(declAsNameEx(varDecl))
    }

    def prime(expression: TlaEx): TBuilderInstruction = {
      createUnsafeInstruction(OperEx(TlaActionOper.prime, expression)(expression.typeTag))
    }

    def declAsNameEx(decl: TlaDecl): TBuilderInstruction = {
      // Untyped declarations should not typically appear, but e.g. tests may generate untyped expressions
      // just assign an arbitrary type in that case
      val declType = if (decl.typeTag == Untyped) BoolT1 else decl.typeTag.asTlaType1()
      builder.name(decl.name, declType)
    }

    def createUnsafeInstruction[T <: TlaEx](ex: T): TBuilderInstruction = {
      ex.asInstanceOf[TlaEx].point[TBuilderInternalState]
    }

    def unchanged(ex: TlaEx): TBuilderInstruction = {
      builder.createUnsafeInstruction(OperEx(TlaActionOper.unchanged, ex)(Typed(BoolT1)))
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

  def setModule(newModule: TlaModule): ModWithPreds = {
    new ModWithPreds(newModule, init, next, loopOK)
  }

  def prependDecl(decl: TlaDecl): ModWithPreds = {
    val newDecls = decl +: module.declarations
    val newModule = new TlaModule(module.name, newDecls)
    setModule(newModule)
  }

  /**
   * Replaces all instances of oldDecl with newDecl
   */
  def replaceDeclInMod(oldDecl: TlaDecl, newDecl: TlaDecl): ModWithPreds = {
    val newDeclarations = module.declarations.map(decl => if (decl.name == oldDecl.name) newDecl else decl)
    val newModule = new TlaModule(module.name, newDeclarations)
    new ModWithPreds(newModule, init, next, loopOK)
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
  def conjunctExToOperDecl(ex: TlaEx, decl: TlaOperDecl, tracker: TransformationTracker): TlaOperDecl = {
    new TlaOperDecl(
        decl.name,
        decl.formalParams,
        Flatten(tracker)(Typed(BoolT1))(
            builder.and(
                builder.createUnsafeInstruction(decl.body),
                builder.createUnsafeInstruction(ex),
            )
        ),
    )(decl.typeTag)
  }
}
