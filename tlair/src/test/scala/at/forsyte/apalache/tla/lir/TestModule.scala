package at.forsyte.apalache.tla.lir

/**
 * Created by jkukovec on 11/16/16.
 */

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs.untyped

@RunWith(classOf[JUnitRunner])
class TestModule extends FunSuite {
  test("AlternatingBit module from Lamport's book") {

    /** CONSTANTS Data */
    val Data = new TlaConstDecl("Data")

    /** VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd */
    val msgQ = new TlaVarDecl("msgQ")
    val ackQ = new TlaVarDecl("ackQ")
    val sBit = new TlaVarDecl("sBit")
    val sAck = new TlaVarDecl("sAck")
    val rBit = new TlaVarDecl("rBit")
    val sent = new TlaVarDecl("sent")
    val rcvd = new TlaVarDecl("rcvd")

    /** Constants {0,1} and <<>> */
    val ZeroOneSet = OperEx(TlaSetOper.enumSet, ValEx(TlaInt(0)), ValEx(TlaInt(1)))
    val emptySeq = OperEx(TlaFunOper.tuple)

    /** --------------------------------------------------------------------------------------------------------------- */

    /**
     * ABInit = /\ msgQ =   <<>>
     * /\ ackQ =   <<>>
     * /\ sBit \in {0,1}
     * /\ sAck =   sBit
     * /\ rBit =   sBit
     * /\ sent \in Data
     * /\ rcvd \in Data
     */
    val ABInit =
      new TlaOperDecl("ABInit", List(),
          OperEx(TlaBoolOper.and, OperEx(TlaOper.eq, NameEx("msgQ"), emptySeq),
              OperEx(TlaOper.eq, NameEx("ackQ"), emptySeq), OperEx(TlaSetOper.in, NameEx("sBit"), ZeroOneSet),
              OperEx(TlaOper.eq, NameEx("sAck"), NameEx("sBit")), OperEx(TlaOper.eq, NameEx("rBit"), NameEx("sBit")),
              OperEx(TlaSetOper.in, NameEx("sBit"), ZeroOneSet), OperEx(TlaSetOper.in, NameEx("sBit"), ZeroOneSet)))

    /**
     * ABTypeInv == /\ msgQ \in Seq( {0,1} \times Data )
     * /\ ackQ \in Seq( {0,1} )
     * /\ sBit \in {0,1}
     * /\ sAck \in {0,1}
     * /\ rBit \in {0,1}
     * /\ sent \in Data
     * /\ rcvd \in Data
     */
    val ABTypeInv =
      new TlaOperDecl("ABTypeInv", List(),
          OperEx(TlaBoolOper.and,
              OperEx(TlaSetOper.in, NameEx("msgQ"),
                  OperEx(TlaSetOper.seqSet, OperEx(TlaSetOper.times, ZeroOneSet, NameEx("Data")))),
              OperEx(TlaSetOper.in, NameEx("ackQ"), OperEx(TlaSetOper.seqSet, ZeroOneSet)),
              OperEx(TlaSetOper.in, NameEx("sBit"), ZeroOneSet), OperEx(TlaSetOper.in, NameEx("sAck"), ZeroOneSet),
              OperEx(TlaSetOper.in, NameEx("rBit"), ZeroOneSet), OperEx(TlaSetOper.in, NameEx("sent"), NameEx("Data")),
              OperEx(TlaSetOper.in, NameEx("rcvd"), NameEx("Data"))))

    /** --------------------------------------------------------------------------------------------------------------- */

    /**
     * SndNewValue(d) == /\ sAck      = sBit
     * /\ sent'     = d
     * /\ sBit'     = 1 - sBit
     * /\ msgQ'     = Append( msgQ, << sBit', d >> )
     * /\ UNCHANGED   << ackQ, sAck, rBit, rcvd >>
     */
    val SndNewValue =
      new TlaOperDecl("SndNewValue", List(SimpleFormalParam("d")),
          OperEx(
              TlaBoolOper.and,
              OperEx(TlaOper.eq, NameEx("sAck"), NameEx("sBit")),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("sent")), NameEx("d")),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("sBit")),
                  OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), NameEx("sBit"))),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("msgQ")),
                  OperEx(TlaSeqOper.append, NameEx("msgQ"),
                      OperEx(TlaFunOper.tuple, OperEx(TlaActionOper.prime, NameEx("sBit")), NameEx("d")))),
              OperEx(TlaActionOper.unchanged,
                  OperEx(TlaFunOper.tuple, NameEx("ackQ"), NameEx("sAck"), NameEx("rBit"), NameEx("rcvd")))
          ))

    /**
     * ReSndMsg == /\ sAck      # sBit
     * /\ msgQ'     = Append( msgQ, << sBit, sent >> )
     * /\ UNCHANGED   << ackQ, sBit, sAck, rBit, sent, rcvd >>
     */
    val ReSndMsg =
      new TlaOperDecl("ReSndMsg", List(),
          OperEx(TlaBoolOper.and, OperEx(TlaOper.ne, NameEx("sAck"), NameEx("sBit")),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("msgQ")),
                  OperEx(TlaSeqOper.append, NameEx("msgQ"), OperEx(TlaFunOper.tuple, NameEx("sBit"), NameEx("sent")))),
              OperEx(TlaActionOper.unchanged,
                  OperEx(TlaFunOper.tuple, NameEx("ackQ"), NameEx("sBit"), NameEx("sAck"), NameEx("rBit"),
                      NameEx("sent"), NameEx("rcvd")))))

    /**
     * RcvMsg == /\ msgQ      # <<>>
     * /\ msgQ'     = Tail( msgQ )
     * /\ rBit'     = Head( msgQ ) [ 1 ]
     * /\ rcvd'     = Head( msgQ ) [ 2 ]
     * /\ UNCHANGED   << ackQ, sBit, sAck, sent >>
     */
    val RcvMsg =
      new TlaOperDecl("RcvMsg", List(),
          OperEx(
              TlaBoolOper.and,
              OperEx(TlaOper.ne, NameEx("msgQ"), emptySeq),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("msgQ")), OperEx(TlaSeqOper.tail, NameEx("msgQ"))),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("rBit")),
                  OperEx(TlaFunOper.app, OperEx(TlaSeqOper.head, NameEx("msgQ")), ValEx(TlaInt(1)))),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("rcvd")),
                  OperEx(TlaFunOper.app, OperEx(TlaSeqOper.head, NameEx("msgQ")), ValEx(TlaInt(2)))),
              OperEx(TlaActionOper.unchanged,
                  OperEx(TlaFunOper.tuple, NameEx("ackQ"), NameEx("sBit"), NameEx("sAck"), NameEx("sent")))
          ))

    /**
     * SndAck == /\ ackQ'     = Append( ackQ, rBit )
     * /\ UNCHANGED   << msgQ, sBit, sAck, rBit, sent, rcvd >>
     */
    val SndAck =
      new TlaOperDecl("SndAck", List(),
          OperEx(TlaBoolOper.and,
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("ackQ")),
                  OperEx(TlaSeqOper.append, NameEx("ackQ"), NameEx("rBit"))),
              OperEx(TlaActionOper.unchanged,
                  OperEx(TlaFunOper.tuple, NameEx("msgQ"), NameEx("sBit"), NameEx("sAck"), NameEx("rBit"),
                      NameEx("sent"), NameEx("rcvd")))))

    /**
     * RcvAck == /\ ackQ      # <<>>
     * /\ ackQ'     = Tail( ackQ )
     * /\ sAck'     = Head( ackQ )
     * /\ UNCHANGED   << msgQ, sBit, rBit, sent, rcvd >>
     */
    val RcvAck =
      new TlaOperDecl("RcvAck", List(),
          OperEx(TlaBoolOper.and, OperEx(TlaOper.ne, NameEx("ackQ"), emptySeq),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("ackQ")), OperEx(TlaSeqOper.tail, NameEx("ackQ"))),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("sAck")), OperEx(TlaSeqOper.head, NameEx("ackQ"))),
              OperEx(TlaActionOper.unchanged,
                  OperEx(TlaFunOper.tuple, NameEx("msgQ"), NameEx("sBit"), NameEx("rBit"), NameEx("sent"),
                      NameEx("rcvd")))))

    /**
     * Lose( q ) == /\ q # <<>>
     * /\ \exists i \in 1 .. Len( q ) :
     * q' = [ j \in 1 .. ( Len( q ) - 1 ) |-> IF j < i THEN q[ j ]
     * ELSE q[ j + 1 ] ]
     * /\ UNCHANGED << sBit, sAck, rBit, sent, rcvd >>
     */
    val Lose =
      new TlaOperDecl("Lose", List(SimpleFormalParam("q")),
          OperEx(TlaBoolOper.exists, NameEx("i"),
              OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)), OperEx(TlaSeqOper.len, NameEx("q"))),
              OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("q")),
                  OperEx(TlaFunOper.funDef, NameEx("j"),
                      OperEx(TlaArithOper.dotdot, ValEx(TlaInt(1)),
                          OperEx(TlaArithOper.minus, OperEx(TlaSeqOper.len, NameEx("q")), ValEx(TlaInt(1)))),
                      OperEx(TlaControlOper.ifThenElse, OperEx(TlaArithOper.lt, NameEx("j"), NameEx("i")),
                          OperEx(TlaFunOper.app, NameEx("q"), NameEx("j")),
                          OperEx(TlaFunOper.app, NameEx("q"),
                              OperEx(TlaArithOper.plus, NameEx("j"), ValEx(TlaInt(1)))))))))

    /**
     * LoseMsg == Lose( msgQ ) /\ UNCHANGED ackQ
     */
    val LoseMsg =
      new TlaOperDecl("LoseMsg", List(),
          OperEx(TlaBoolOper.and, OperEx(TlaOper.apply, NameEx("Lose"), NameEx("msgQ")),
              OperEx(TlaActionOper.unchanged, NameEx("ackQ"))))

    /**
     * LoseAck == Lose( ackQ ) /\ UNCHANGED msgQ
     */
    val LoseAck =
      new TlaOperDecl("LoseAck", List(),
          OperEx(TlaBoolOper.and, OperEx(TlaOper.apply, NameEx("Lose"), NameEx("ackQ")),
              OperEx(TlaActionOper.unchanged, NameEx("msgQ"))))

    /**
     * ABNext == \/ \exists d \in Data : SndNewValue(d)
     * \/ ReSndMsg \/ RcvMsg \/ SndAck \/ RcvAck
     * \/ LoseMsg \/ LoseAck
     */
    val ABNext =
      new TlaOperDecl("ABNext", List(),
          OperEx(TlaBoolOper.or,
              OperEx(TlaBoolOper.exists, NameEx("d"), NameEx("Data"),
                  OperEx(TlaOper.apply, NameEx("SndNewValue"), NameEx("d"))), NameEx("ReSndMsg"), NameEx("RcvMsg"),
              NameEx("SndAck"), NameEx("RcvAck"), NameEx("LoseMsg"), NameEx("LoseAck")))

    /** --------------------------------------------------------------------------------------------------------------- */

    /**
     * abvars == << msgQ, ackQ, sBit, sAck, rBit, sent, rcvd >>
     */
    val abvars =
      new TlaOperDecl("abvars", // NOTE: Is this really an operator? Seems contrived.
          List(),
          OperEx(TlaFunOper.tuple, NameEx("msgQ"), NameEx("ackQ"), NameEx("sBit"), NameEx("sAck"), NameEx("rBit"),
              NameEx("sent"), NameEx("rcvd")))

    /**
     * ABFairness == /\ WF_abvars( ReSndMsg ) /\ WF_abvars( SndAck )
     * /\ SF_abvars( RcvMsg ) /\ SF_abvars( RcvAck )
     */
    val ABFairness =
      new TlaOperDecl("AbFairness", List(),
          OperEx(TlaBoolOper.and, OperEx(TlaTempOper.weakFairness, NameEx("abvars"), NameEx("ReSndMsg")),
              OperEx(TlaTempOper.weakFairness, NameEx("abvars"), NameEx("SndAck")),
              OperEx(TlaTempOper.strongFairness, NameEx("abvars"), NameEx("RcvMsg")),
              OperEx(TlaTempOper.strongFairness, NameEx("abvars"), NameEx("RcvAck"))))

    /** --------------------------------------------------------------------------------------------------------------- */

    /**
     * ABSpec == ABInit /\ [][ABNext]_abvars /\ ABFairness
     */

    val ABSpec =
      new TlaOperDecl("ABSpec", List(),
          OperEx(TlaBoolOper.and, NameEx("ABInit"), OperEx(TlaActionOper.stutter, NameEx("ABNext"), NameEx("abvars")),
              NameEx("ABFairness")))

    /** --------------------------------------------------------------------------------------------------------------- */

    /**
     * THEOREM ABSpec => []( ABTypeInv )
     */

  }
}
