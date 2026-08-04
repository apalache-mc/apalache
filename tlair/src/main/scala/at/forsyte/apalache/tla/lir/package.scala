package at.forsyte.apalache.tla

package object lir {

  /**
   * Find the body of an operator declaration by the operator name.
   *
   * @param p_opName
   *   the name of the operator to look up
   * @param decls
   *   the declarations to search
   * @return
   *   the body of the operator, or [[NullEx]] if no operator declaration carries that name
   */
  def findBodyOf(p_opName: String, decls: TlaDecl*): TlaEx = {
    decls
      .find {
        _.name == p_opName
      }
      .withFilter(_.isInstanceOf[TlaOperDecl])
      .map(_.asInstanceOf[TlaOperDecl].body)
      .getOrElse(NullEx)
  }
}
