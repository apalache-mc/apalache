package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.transformations.LanguagePred

/**
  * <p>Test whether the expressions fit into the flat fragment: all calls to user operators are inlined,
  * except the calls to nullary let-in definitions.</p>
  *
  * <p>To get a better idea of the accepted fragment, check TestFlatLanguagePred.</p>
  *
  * @see TestFlatLanguagePred
  * @author Igor Konnov
  */
class FlatLanguagePred extends LanguagePred {
  override def isModuleOk(mod: TlaModule): Boolean = {
    mod.operDeclarations.forall(d => isExprOk(d.body))
  }

  override def isExprOk(expr: TlaEx): Boolean = {
    isOkInContext(Set(), expr)
  }

  private def isOkInContext(letDefs: Set[String], expr: TlaEx): Boolean = {
    expr match {
      case LetInEx(body, defs@_*) =>
        // go inside the let definitions
        def eachDefRec(ctx: Set[String], ds: Seq[TlaOperDecl]): Boolean = {
          if (ds.nonEmpty) {
            // check the declaration body first
            if (isOkInContext(ctx, ds.head.body)) {
              // then save that the let definition is ok and continue
              eachDefRec(ctx + ds.head.name, ds.tail)
            } else {
              false
            }
          } else {
            true
          }
        }

        val newLetDefs = defs.map(_.name).toSet
        isOkInContext(newLetDefs, body)

      case OperEx(TlaOper.apply, NameEx(opName), args@_*) =>
        // the only allowed case is calling a nullary operator that was declared with let-in
        args.isEmpty && letDefs.contains(opName)

      case OperEx(_, args @ _*) =>
        // check the arguments recursively
        args forall(e => isOkInContext(letDefs, e))

      case _ => true
    }
  }
}

object FlatLanguagePred {
  def apply(): FlatLanguagePred = {
    new FlatLanguagePred
  }
}