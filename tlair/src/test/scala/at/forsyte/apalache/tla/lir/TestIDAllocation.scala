package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaTrue, TlaFalse}

import at.forsyte.apalache.tla.lir.plugins.{Identifier, BasicSubstitutions}
import at.forsyte.apalache.tla.lir.db.EquivalenceDB


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
      * /\ sent'     = d
      * /\ sBit'     = 1 - sBit
      * /\ msgQ'     = Append( msgQ, << sBit', d >> )
      * /\ UNCHANGED   << ackQ, sAck, rBit, rcvd >>
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



    val sum = OperEx( TlaOper.eq,
      OperEx( TlaArithOper.plus, ValEx( TlaInt( 4 ) ), ValEx( TlaInt( 0 ) ) ),
      OperEx( TlaArithOper.plus, ValEx( TlaInt( 2 ) ), ValEx( TlaInt( 2 ) ) )
    )

    val spec = new TlaSpec( "someSum", List( TlaOperDecl( "", List( ), sum ) ) )

    //val spec = new TlaSpec("Test spec.", List(SndNewValue))
//    Cleaner.clean( spec )

    def show( thisSpec : TlaSpec) = {
      thisSpec.declarations.foreach(
        x => x match {
          case TlaOperDecl( _, _, ex ) => println( ex )
        }
      )
    }

    /*
    println( "With computable addition\n" )
    show( spec )

    println( "\nFully reduced" )
    show( Cleaner.clean( BasicSubstitutions.sub( spec ) ) )
    */


    val redundantbool = OperEx( TlaOper.eq,
      OperEx( TlaBoolOper.and, NameEx( "x" ), ValEx( TlaTrue ) ),
      OperEx( TlaBoolOper.or, ValEx( TlaFalse ), NameEx( "x" ) )
    )



    val spec2 = new TlaSpec( "boolSimplification", List( TlaOperDecl( "", List( ), redundantbool ) ) )
    println( "\nRedundant bool\n" )
    val spc = Identifier.identify( spec2 )
    show( spc )
    println( "\nFully reduced" )
    show( Identifier.identify( BasicSubstitutions.sub( spec2 ) ) )


    val eqdb : EquivalenceDB = new EquivalenceDB

    eqdb.processAll(spc)

    println("\n")
    for( a <- 0 until 12 ){ //Cleaner.nAllocated() ){
      println( UID( a ) +  " -> " +  eqdb( UID( a ) ).getOrElse( None ) )
    }



  }
}
