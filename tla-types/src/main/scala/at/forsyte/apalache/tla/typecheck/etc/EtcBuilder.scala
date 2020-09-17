package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.UID
import at.forsyte.apalache.tla.typecheck._

/**
  * A builder trait to conveniently construct instances STCExpr.
  * Mix this trait to your class to construct STC expressions without pain.
  * This class shields the user from the weird syntax of case classes that have two kinds of fields:
  * the fields counted in equals, and the fields that are ignored in equals.
  *
  * @author Igor Konnov
  */
trait EtcBuilder {
  def mkConst(id: UID, tt: TlaType1): EtcConst = {
    EtcConst(tt) (id)
  }

  def mkUniqConst(tt: TlaType1): EtcConst = {
    mkConst(UID.unique, tt)
  }

  def mkName(id: UID, name: String): EtcName = {
    EtcName(name) (id)
  }

  def mkUniqName(name: String): EtcName = {
    mkName(UID.unique, name)
  }

  def mkAbs(id: UID, body: EtcExpr, paramsAndDoms: (String, EtcExpr)*): EtcAbs = {
    EtcAbs(body, paramsAndDoms :_*) (id)
  }

  def mkUniqAbs(body: EtcExpr, paramsAndDoms: (String, EtcExpr)*): EtcAbs = {
    mkAbs(UID.unique, body, paramsAndDoms :_*)
  }

  def mkApp(id: UID, operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    EtcApp(operTypes, args :_*) (id)
  }

  def mkUniqApp(operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    mkApp(UID.unique, operTypes, args :_*)
  }

  def mkAppByName(id: UID, name: String, args: EtcExpr*): EtcAppByName = {
    EtcAppByName(name, args :_*) (id)
  }

  def mkUniqAppByName(name: String, args: EtcExpr*): EtcAppByName = {
    mkAppByName(UID.unique, name, args :_*)
  }

  def mkLet(id: UID, name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    EtcLet(name, bound, body) (id)
  }

  def mkUniqLet(name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    mkLet(UID.unique, name, bound, body)
  }
}
