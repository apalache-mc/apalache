package at.forsyte.apalache.tla.lir

/**
  * Created by jkukovec on 11/16/16.
  */

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt

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

    val ZeroOneSet = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(0)), ValEx(TlaInt(1)))
    val emptySeq = OperEx(TlaSeqOper.enumSeq)



    val ABInt =
        new TlaOperDecl("ABInt",
                        List(),
                        OperEx(TlaBoolOper.and,
                               OperEx(TlaOper.eq,
                                      NameEx("msgQ"),
                                      emptySeq
                                      ),
                               OperEx(TlaOper.eq,
                                      NameEx("ackQ"),
                                      emptySeq
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("sBit"),
                                      ZeroOneSet
                                      ),
                               OperEx(TlaOper.eq,
                                      NameEx("sAck"),
                                      NameEx("sBit")
                                      ),
                               OperEx(TlaOper.eq,
                                      NameEx("rBit"),
                                      NameEx("sBit")
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("sBit"),
                                      ZeroOneSet
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("sBit"),
                                      ZeroOneSet
                                      )
                               )
                        )

    val ABTypeInv =
        new TlaOperDecl("ABTypeInv",
                        List(),
                        OperEx(TlaBoolOper.and,
                               OperEx(TlaSetOper.in,
                                      NameEx("msgQ"),
                                      OperEx(TlaSetOper.seqSet,
                                             OperEx(TlaSetOper.product,
                                                    ZeroOneSet,
                                                    NameEx("Data")
                                                    )
                                             )
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("ackQ"),
                                      OperEx(TlaSetOper.seqSet,
                                             ZeroOneSet
                                             )
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("sBit"),
                                      ZeroOneSet
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("sAck"),
                                      ZeroOneSet
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("rBit"),
                                      ZeroOneSet
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("sent"),
                                      NameEx("Data")
                                      ),
                               OperEx(TlaSetOper.in,
                                      NameEx("rcvd"),
                                      NameEx("Data")
                                      )
                               )
                        )

    val SndNewValue =
        new TlaOperDecl("SndNewValue",
                        List(SimpleFormalParam("d")),
                        OperEx(TlaBoolOper.and,
                               OperEx(TlaOper.eq,
                                      NameEx("sAck"),
                                      NameEx("sBit")
                                      ),
                               OperEx(TlaOper.eq,
                                      OperEx(TlaActionOper.prime,
                                             NameEx("sent")
                                             ),
                                      NameEx("d")
                                      ),
                               OperEx(TlaOper.eq,
                                      OperEx(TlaActionOper.prime,
                                           NameEx("sBit")
                                           ),
                                      OperEx(TlaArithmeticOper.minus,
                                           ValEx(TlaInt(1)),
                                           NameEx("sBit")
                                           )
                                      ),
                               OperEx(TlaOper.eq,
                                      OperEx(TlaActionOper.prime,
                                             NameEx("msgQ")
                                             ),
                                      OperEx(TlaSeqOper.append,
                                             NameEx("msgQ"),
                                             OperEx(TlaSeqOper.enumSeq,
                                                    OperEx(TlaActionOper.prime,
                                                           NameEx("sBit")
                                                    ),
                                                    NameEx("d")
                                                    )
                                             )
                                      ),
                               OperEx(TlaActionOper.unchanged,
                                      OperEx(TlaSeqOper.enumSeq,
                                             NameEx("ackQ"),
                                             NameEx("sAck"),
                                             NameEx("rBit"),
                                             NameEx("rcvd")
                                             )
                                      )
                               )
                        )

    val ReSndMsg =
        new TlaOperDecl("ReSndMsg",
                        List(),
                        OperEx(TlaBoolOper.and,
                               OperEx(TlaOper.ne,
                                      NameEx("sAck"),
                                      NameEx("sBit")
                                      ),
                               OperEx(TlaOper.eq,
                                      OperEx(TlaActionOper.prime,
                                             NameEx("msgQ")
                                             ),
                                      OperEx(TlaSeqOper.append,
                                             NameEx("msgQ"),
                                             OperEx(TlaSeqOper.enumSeq,
                                                    NameEx("sBit"),
                                                    NameEx("sent")
                                                    )
                                             )
                                      ),
                               OperEx(TlaActionOper.unchanged,
                                      OperEx(TlaSeqOper.enumSeq,
                                             NameEx("ackQ"),
                                             NameEx("sBit"),
                                             NameEx("sAck"),
                                             NameEx("rBit"),
                                             NameEx("sent"),
                                             NameEx("rcvd")
                                             )
                                      )
                               )
                        )
    val RcvMsg =
        new TlaOperDecl("RcvMsg",
                        List(),
                        OperEx(TlaBoolOper.and,
                               OperEx(TlaOper.ne,
                                      NameEx("msgQ"),
                                      emptySeq
                                      ),
                               OperEx(TlaOper.eq,
                                      OperEx(TlaActionOper.prime,
                                             NameEx("msgQ")
                                             ),
                                      OperEx(TlaSeqOper.tail,
                                             NameEx("msgQ")
                                             )
                                      ),
                               OperEx(TlaOper.eq,
                                      OperEx(TlaActionOper.prime,
                                             NameEx("rBit")
                                             ),
                                      OperEx(TlaFunOper.app,
                                             OperEx(TlaSeqOper.head,
                                                    NameEx("msgQ")
                                                    ),
                                             ValEx(TlaInt(1))
                                             )
                                      ),
                               OperEx(TlaOper.eq,
                                      OperEx(TlaActionOper.prime,
                                             NameEx("rcvd")
                                             ),
                                      OperEx(TlaFunOper.app,
                                             OperEx(TlaSeqOper.head,
                                             NameEx("msgQ")
                                             ),
                                             ValEx(TlaInt(2))
                                             )
                                      ),
                               OperEx(TlaActionOper.unchanged,
                                      OperEx(TlaSeqOper.enumSeq,
                                             NameEx("ackQ"),
                                             NameEx("sBit"),
                                             NameEx("sAck"),
                                             NameEx("sent")
                                             )
                                      )
                               )
                        )



  }

}
