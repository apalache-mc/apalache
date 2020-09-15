package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.UID

/**
  * A builder trait to conveniently construct instances STCExpr.
  * Mix this trait to your class to construct STC expressions without pain.
  * This class shields the user from the weird syntax of case classes that have two kinds of fields:
  * the fields counted in equals, and the fields that are ignored in equals.
  *
  * @author Igor Konnov
  */
trait STCBuilder {
  def mkConst(id: UID, types: TlaType1*): STCConst = {
    STCConst(types :_*) (id)
  }

  def mkUniqConst(types: TlaType1*): STCConst = {
    mkConst(UID.unique, types :_*)
  }

  def mkName(id: UID, name: String): STCName = {
    STCName(name) (id)
  }

  def mkUniqName(name: String): STCName = {
    mkName(UID.unique, name)
  }

  def mkAbs(id: UID, body: STCExpr, paramsAndDoms: (String, STCExpr)*): STCAbs = {
    STCAbs(body, paramsAndDoms :_*) (id)
  }

  def mkUniqAbs(body: STCExpr, paramsAndDoms: (String, STCExpr)*): STCAbs = {
    mkAbs(UID.unique, body, paramsAndDoms :_*)
  }

  def mkApp(id: UID, oper: STCExpr, args: STCExpr*): STCApp = {
    STCApp(oper, args :_*) (id)
  }

  def mkUniqApp(oper: STCExpr, args: STCExpr*): STCApp = {
    mkApp(UID.unique, oper, args :_*)
  }

  def mkLet(id: UID, name: String, bound: STCExpr, body: STCExpr): STCLet = {
    STCLet(name, bound, body) (id)
  }

  def mkUniqLet(name: String, bound: STCExpr, body: STCExpr): STCLet = {
    mkLet(UID.unique, name, bound, body)
  }

  def mkIntro(id: UID, name: String, scope: STCExpr): STCIntroTypeVar = {
    STCIntroTypeVar(name, scope) (id)
  }

  def mkUniqIntro(name: String, scope: STCExpr): STCIntroTypeVar = {
    mkIntro(UID.unique, name, scope)
  }
}
