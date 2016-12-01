package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.cleaner.Cleaner

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Created by jkukovec on 11/30/16.
  */

@RunWith(classOf[JUnitRunner])
class TestIDAllocation extends FunSuite{

  test("Check ID allocation for basic operator") {

    /**
      * SndNewValue(d) == /\ sAck      = sBit
      *                   /\ sent'     = d
      *                   /\ sBit'     = 1 - sBit
      *                   /\ msgQ'     = Append( msgQ, << sBit', d >> )
      *                   /\ UNCHANGED   << ackQ, sAck, rBit, rcvd >>
      */
    val SndNewValue =
      new TlaOperDecl( "SndNewValue",
        List( SimpleFormalParam( "d" ) ),
        OperEx( TlaBoolOper.and,
          OperEx( TlaOper.eq,
            NameEx( "sAck" ),
            NameEx( "sBit" )
          ),
          OperEx( TlaOper.eq,
            OperEx( TlaActionOper.prime,
              NameEx( "sent" )
            ),
            NameEx( "d" )
          ),
          OperEx( TlaOper.eq,
            OperEx( TlaActionOper.prime,
              NameEx( "sBit" )
            ),
            OperEx( TlaArithOper.minus,
              ValEx( TlaInt( 1 ) ),
              NameEx( "sBit" )
            )
          ),
          OperEx( TlaOper.eq,
            OperEx( TlaActionOper.prime,
              NameEx( "msgQ" )
            ),
            OperEx( TlaSeqOper.append,
              NameEx( "msgQ" ),
              OperEx( TlaFunOper.tuple,
                OperEx( TlaActionOper.prime,
                  NameEx( "sBit" )
                ),
                NameEx( "d" )
              )
            )
          ),
          OperEx( TlaActionOper.unchanged,
            OperEx( TlaFunOper.tuple,
              NameEx( "ackQ" ),
              NameEx( "sAck" ),
              NameEx( "rBit" ),
              NameEx( "rcvd" )
            )
          )
        )
      )



    val dummy = OperEx( TlaOper.eq,
      OperEx( TlaArithOper.plus, ValEx( TlaInt(2) ), ValEx( TlaInt(1) ) ),
      OperEx( TlaArithOper.plus, ValEx( TlaInt(1) ), ValEx( TlaInt(2) ) )
    )

    //val spec = new TlaSpec("eghkdfj", List(TlaOperDecl( "", List(), dummy)))

    val spec = new TlaSpec("Test spec.", List(SndNewValue))
    Cleaner.clean( spec )

    spec.declarations.foreach(
      x => x match{
        case TlaOperDecl( _, _, ex) => println( ex )
      }
    )

  }
}
