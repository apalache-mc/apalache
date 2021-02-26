package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.{TlaDeclTransformation, TlaExTransformation, TransformationTracker}

/**
 * DeepCopy constructs a structurally identical copy of a given TlaEx or TlaDecl, with fresh unique IDs.
 */
class DeepCopy(tracker: TransformationTracker) {
  def deepCopyDecl[T <: TlaDecl](decl: T): T = deepCopyDeclInternal(decl).asInstanceOf[T]

  private def deepCopyDeclInternal: TlaDeclTransformation = tracker.trackDecl {
    case d @ TlaAssumeDecl(bodyEx)      => TlaAssumeDecl(deepCopyEx(bodyEx))(d.typeTag)
    case d @ TlaTheoremDecl(name, body) => TlaTheoremDecl(name, deepCopyEx(body))(d.typeTag)
    case d @ TlaVarDecl(name)           => TlaVarDecl(name)(d.typeTag)
    case d @ TlaOperDecl(name, formalParams, body) =>
      val decl = TlaOperDecl(name, formalParams, deepCopyEx(body))(d.typeTag)
      decl.isRecursive = d.isRecursive
      decl
    case d @ TlaConstDecl(name) => TlaConstDecl(name)(d.typeTag)
  }

  def deepCopyEx[T <: TlaEx](ex: T): T = deepCopyExInternal(ex).asInstanceOf[T]

  private def deepCopyExInternal: TlaExTransformation = tracker.trackEx {
    case NullEx        => NullEx
    case e @ ValEx(v)  => ValEx(v)(e.typeTag)
    case e @ NameEx(n) => NameEx(n)(e.typeTag)
    case e @ LetInEx(body, decls @ _*) =>
      LetInEx(deepCopyEx(body), decls map deepCopyDecl: _*)(e.typeTag)
    case e @ OperEx(oper, args @ _*) =>
      OperEx(oper, args map deepCopyEx: _*)(e.typeTag)
  }

  def deepCopyModule(module: TlaModule) = new TlaModule(module.name, module.declarations map deepCopyDecl)
}

object DeepCopy {
  def apply(tracker: TransformationTracker): DeepCopy = {
    new DeepCopy(tracker)
  }
}
