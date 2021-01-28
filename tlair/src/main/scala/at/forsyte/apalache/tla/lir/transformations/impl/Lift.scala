package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.TlaExTransformation

object Lift {
  def exToDecl(tr: TlaExTransformation): TlaDecl => TlaDecl = {
    case d @ TlaOperDecl(_, _, b) => d.copy(body = tr(b))
    case d                        => d
  }

  def declToDecls(
      tr: TlaDecl => TlaDecl
  ): Traversable[TlaDecl] => Traversable[TlaDecl] =
    _ map tr

  def exToDecls(
      tr: TlaExTransformation
  ): Traversable[TlaDecl] => Traversable[TlaDecl] =
    _ map exToDecl(tr)
}
