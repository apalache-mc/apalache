package at.forsyte.apalache.tla.lir

/**
  * Created by jkukovec on 11/16/16.
  */

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef.{TlaIntSet, TlaEmptySet}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaUserSet, TlaStr, TlaInt,TlaFiniteValSet}
import at.forsyte.apalache.tla.lir.{TlaConstDecl,TlaVarDecl,TlaOperDecl}

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith(classOf[JUnitRunner])
class TestModule extends FunSuite{
  test("AlternatingBit module from Lamport's book") {
    val Data = new TlaConstDecl("Data")
    val msgQ = new TlaVarDecl("msgQ")
    val ackQ = new TlaVarDecl("ackQ")
    val sBit = new TlaVarDecl("sBit")
    val sAck = new TlaVarDecl("sAck")
    val rBit = new TlaVarDecl("rBit")
    val sent = new TlaVarDecl("sent")
    val rcvd = new TlaVarDecl("rcvd")

    val ZeroOneSet = new OperEx(TlaSetOper.enumSet, ValEx(TlaInt(0)), ValEx(TlaInt(1)))



    val ABInt = new TlaOperDecl("ABInt",
                                List() ,
                                OperEx(TlaBoolOper.and,
                                  OperEx(TlaOper.eq,NameEx("msgQ"),EMPTYSEQ),
                                  OperEx(TlaOper.eq,NameEx("ackQ"),EMPTYSEQ),
                                  OperEx(TlaSetOper.in,NameEx("sBit"),ZeroOneSet),
                                  OperEx(TlaOper.eq,NameEx("sAck"),NameEx("sBit")),
                                  OperEx(TlaOper.eq,NameEx("rBit"),NameEx("sBit")),
                                  OperEx(TlaSetOper.in,NameEx("sBit"),ZeroOneSet),
                                  OperEx(TlaSetOper.in,NameEx("sBit"),ZeroOneSet)
                                  )
                                )

    val ABTypeInv = new TlaOperDecl("ABTypeInv",
                                    List() ,
                                    OperEx(TlaBoolOper.and,
                                      OperEx(TlaSetOper.in,NameEx("msgQ"),SEQUENCE),
                                      OperEx(TlaSetOper.in,NameEx("msgQ"),SEQUENCE),
                                      OperEx(TlaSetOper.in,NameEx("msgQ"),ZeroOneSet),
                                      OperEx(TlaSetOper.in,NameEx("msgQ"),ZeroOneSet),
                                      OperEx(TlaSetOper.in,NameEx("msgQ"),ZeroOneSet),
                                      OperEx(TlaSetOper.in,NameEx("msgQ"),NameEx("Data")),
                                      OperEx(TlaSetOper.in,NameEx("msgQ"),NameEx("Data"))
                                      )
                                    )

    val SndNewValue = new TlaOperDecl("SndNewValue",
                                      List(SimpleFormalParam("d")),
                                      OperEx(TlaBoolOper.and,
                                        OperEx(TlaOper.eq,NameEx("sAck"),NameEx("sBit")),
                                        OperEx(TlaOper.eq,OperEx(TlaActionOper.tlaPrime, NameEx("sent")),NameEx("d")),
                                        OperEx(TlaOper.eq,OperEx(TlaActionOper.tlaPrime, NameEx("sBit")),OperEx(TlaArithmeticOper.minus,ValEx(TlaInt(1)),NameEx("sBit"))),
                                        OperEx(TlaOper.eq,OperEx(TlaActionOper.tlaPrime, NameEx("msgQ")),APPEND_CALL),
                                        OperEx(TlaActionOper.tlaUnchanged,SEQUENCE)
                                        )
                                      )




  }

}
