package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.{TlaType1, UID}
import at.forsyte.apalache.tla.typecheck._

/**
 * A builder trait to conveniently construct instances of EtcExpr.
 * Mix this trait to your class to construct Etc expressions without pain.
 * This class shields the user from the weird syntax of case classes that have two kinds of fields:
 * the fields counted in equals, and the fields that are ignored in equals.
 *
 * @author Igor Konnov
 */
trait EtcBuilder {
  protected def mkConst(sourceRef: EtcRef, tt: TlaType1): EtcConst = {
    EtcConst(tt)(sourceRef)
  }

  protected def mkUniqConst(tt: TlaType1): EtcConst = {
    mkConst(ExactRef(UID.unique), tt)
  }

  protected def mkBlameConst(tt: TlaType1): EtcConst = {
    mkConst(BlameRef(UID.unique), tt)
  }

  protected def mkName(sourceRef: EtcRef, name: String): EtcName = {
    EtcName(name)(sourceRef)
  }

  protected def mkUniqName(name: String): EtcName = {
    mkName(ExactRef(UID.unique), name)
  }

  protected def mkBlameName(name: String): EtcName = {
    mkName(BlameRef(UID.unique), name)
  }

  protected def mkAbs(sourceRef: EtcRef, body: EtcExpr, paramsAndDoms: (EtcName, EtcExpr)*): EtcAbs = {
    EtcAbs(body, paramsAndDoms: _*)(sourceRef)
  }

  protected def mkUniqAbs(body: EtcExpr, paramsAndDoms: (EtcName, EtcExpr)*): EtcAbs = {
    mkAbs(ExactRef(UID.unique), body, paramsAndDoms: _*)
  }

  protected def mkBlameAbs(body: EtcExpr, paramsAndDoms: (EtcName, EtcExpr)*): EtcAbs = {
    mkAbs(BlameRef(UID.unique), body, paramsAndDoms: _*)
  }

  protected def mkApp(sourceRef: EtcRef, operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    EtcApp(operTypes, args: _*)(sourceRef)
  }

  protected def mkUniqApp(operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    mkApp(ExactRef(UID.unique), operTypes, args: _*)
  }

  protected def mkBlameApp(operTypes: Seq[TlaType1], args: EtcExpr*): EtcApp = {
    mkApp(BlameRef(UID.unique), operTypes, args: _*)
  }

  protected def mkAppByName(sourceRef: EtcRef, name: EtcName, args: EtcExpr*): EtcAppByName = {
    EtcAppByName(name, args: _*)(sourceRef)
  }

  protected def mkUniqAppByName(name: EtcName, args: EtcExpr*): EtcAppByName = {
    mkAppByName(ExactRef(UID.unique), name, args: _*)
  }

  protected def mkBlameAppByName(name: EtcName, args: EtcExpr*): EtcAppByName = {
    mkAppByName(BlameRef(UID.unique), name, args: _*)
  }

  protected def mkLet(sourceRef: EtcRef, name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    EtcLet(name, bound, body)(sourceRef)
  }

  protected def mkUniqLet(name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    mkLet(ExactRef(UID.unique), name, bound, body)
  }

  protected def mkBlameLet(name: String, bound: EtcExpr, body: EtcExpr): EtcLet = {
    mkLet(BlameRef(UID.unique), name, bound, body)
  }

  protected def mkTypeDecl(sourceRef: EtcRef, name: String, declaredType: TlaType1, scopedEx: EtcExpr): EtcTypeDecl = {
    EtcTypeDecl(name, declaredType, scopedEx)(sourceRef)
  }

  protected def mkUniqTypeDecl(name: String, declaredType: TlaType1, scopedEx: EtcExpr): EtcTypeDecl = {
    mkTypeDecl(ExactRef(UID.unique), name, declaredType, scopedEx)
  }

  protected def mkBlameTypeDecl(name: String, declaredType: TlaType1, scopedEx: EtcExpr): EtcTypeDecl = {
    mkTypeDecl(BlameRef(UID.unique), name, declaredType, scopedEx)
  }
}
