package at.forsyte.apalache.tla.pp.temporal

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir.transformations.standard.Flatten
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1

object ScopedBuilderExtensions {
  implicit class ScopedBuilderExtension(val builder: ScopedBuilder) {
    def declAsNameEx(decl: TlaDecl): TBuilderInstruction = {
      builder.name(decl.name, decl.typeTag.asTlaType1())
    }
  }
}

/**
 * A convenience class storing a module, together with the init, next and loopOK predicates of that module. Useful to
 * avoid re-finding these predicates.
 */
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
  import at.forsyte.apalache.tla.pp.temporal.utils.builder

  /**
   * Takes decl, ex and returns newDecl with the same name as decl, with its body extended like this: newDecl == decl /\
   * ex
   */
  def andInDecl(ex: TBuilderInstruction, decl: TlaOperDecl, tracker: TransformationTracker): TlaOperDecl = {
    val newBody =
      Flatten(tracker)(Typed(BoolT1))(
          builder.and(
              builder.useTrustedEx(decl.body),
              ex,
          )
      )
    decl.copy(body = newBody)
  }
}
