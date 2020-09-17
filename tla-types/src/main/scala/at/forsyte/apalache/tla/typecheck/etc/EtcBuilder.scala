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
  def mkConst(sourceRef: EtcRef, tt: TlaType1): EtcConst = {
    EtcConst(tt) (sourceRef)
  }

  def mkUniqConst(tt: TlaType1): EtcConst = {
    mkConst(ExactRef(UID.unique), tt)
  }

  def mkBlameConst(tt: TlaType1): EtcConst = {
    mkConst(BlameRef(UID.unique), tt)
  }

  def mkName(sourceRef: EtcRef, name: String): EtcName = {
    EtcName(name) (sourceRef)
  }

  def mkUniqName(name: String): EtcName = {
    mkName(ExactRef(UID.unique), name)
  }

  def mkBlameName(name: String): EtcName = {
    mkName(BlameRef(UID.unique), name)
  }

  def mkAbs(sourceRef: EtcRef, body: EtcExpr, paramsAndDoms: (String, EtcExpr)*): EtcAbs = {
    EtcAbs(body, paramsAndDoms :_*) (sourceRef)
  }

  def mkUniqAbs(body: EtcExpr, paramsAndDoms: (String, EtcExpr)*): EtcAbs = {
    mkAbs(ExactRef(UID.unique), body, paramsAndDoms :_*)
  }

  def mkBlameAbs(body: EtcExpr, paramsAndDoms: (String, EtcExpr)*): EtcAbs = {
    mkAbs(BlameRef(UID.unique), body, paramsAndDoms :_*)
  }

  def mkApp(sourceRef: EtcRef, operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    EtcApp(operTypes, args :_*) (sourceRef)
  }

  def mkUniqApp(operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    mkApp(ExactRef(UID.unique), operTypes, args :_*)
  }

  def mkBlameApp(operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    mkApp(BlameRef(UID.unique), operTypes, args :_*)
  }

  def mkAppByName(sourceRef: EtcRef, name: String, args: EtcExpr*): EtcAppByName = {
    EtcAppByName(name, args :_*) (sourceRef)
  }

  def mkUniqAppByName(name: String, args: EtcExpr*): EtcAppByName = {
    mkAppByName(ExactRef(UID.unique), name, args :_*)
  }

  def mkBlameAppByName(name: String, args: EtcExpr*): EtcAppByName = {
    mkAppByName(BlameRef(UID.unique), name, args :_*)
  }

  def mkLet(sourceRef: EtcRef, name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    EtcLet(name, bound, body) (sourceRef)
  }

  def mkUniqLet(name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    mkLet(ExactRef(UID.unique), name, bound, body)
  }

  def mkBlameLet(name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    mkLet(BlameRef(UID.unique), name, bound, body)
  }
}
