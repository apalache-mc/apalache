package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaTrue, TlaFalse}

import at.forsyte.apalache.tla.lir.plugins.{Identifier, BasicSubstitutions, OperatorSubstitution, OperatorDB}
import at.forsyte.apalache.tla.lir.db.{EquivalenceDB}


import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Created by jkukovec on 11/30/16.
  */

@RunWith(classOf[JUnitRunner])
class TestIDAllocation extends FunSuite{

  def show( thisSpec : TlaSpec) = {
    thisSpec.declarations.foreach(
      x => x match {
        case TlaOperDecl( _, _, ex ) => println( ex )
      }
    )
  }

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

  val sum = OperEx( TlaOper.eq,
    OperEx( TlaArithOper.plus, ValEx( TlaInt( 4 ) ), ValEx( TlaInt( 0 ) ) ),
    OperEx( TlaArithOper.plus, ValEx( TlaInt( 2 ) ), ValEx( TlaInt( 2 ) ) )
  )

  val redundantbool = OperEx( TlaOper.eq,
    OperEx( TlaBoolOper.and, NameEx( "x" ), ValEx( TlaTrue ) ),
    OperEx( TlaBoolOper.or, ValEx( TlaFalse ), NameEx( "x" ) )
  )


  val specSnd = new TlaSpec("Test spec.", List(SndNewValue))
  val specSum = new TlaSpec( "someSum", List( TlaOperDecl( "", List( ), sum ) ) )
  val specBool = new TlaSpec( "boolSimplification", List( TlaOperDecl( "", List( ), redundantbool ) ) )

  ignore("Check ID allocation for basic operator") {

    val spec = specSnd

    Identifier.reset()

    println( "\nspecSnd before: \n" )
    show( spec )

    println( "\nspecSnd after: \n" )
    show( Identifier.identify( spec ) )

    Identifier.reset()


  }

  ignore("Check basic substitution") {

    val spec = specSum

    Identifier.reset()

    println( "\nspecSum before:\n" )
    show( spec )

    println( "\nspecSum after: \n" )
    show( Identifier.identify( BasicSubstitutions.sub( spec ) ) )

    val spec2 = specBool

    println( "\nspecBool before:\n" )
    show( spec2 )

    println( "\nspecBool after: \n" )
    show( Identifier.identify( BasicSubstitutions.sub( spec2 ) ) )

    Identifier.reset()


  }

  ignore("Check equivalence") {

    val spec = specSnd
    Identifier.reset()

    Identifier.identify( spec )

    println( "\nspec: \n" )
    show( specSnd )

    EquivalenceDB.processAll( spec )

    println("\nEquivalence IDs/classes: \n")
    for( a <- 0 until EquivalenceDB.size() ){
      println( UID( a ) +  " -> " +  EquivalenceDB( UID( a ) ).getOrElse( None ) + " , " + EquivalenceDB.getEqClass( UID( a ) ).getOrElse( None ))
    }

    EquivalenceDB.reset()

  }

  ignore( "check attributes" ){

    EquivalenceDB.reset()
    Identifier.reset()

    val a1 = NameEx( "a" )
    val a2 = NameEx( "a" )

    a1.ID = UID( 99 )
    a2.ID = UID( 42 )

    val spec = new TlaSpec( "attributes", List( TlaOperDecl( "A1", List( ), a1 ), TlaOperDecl( "A2", List( ), a2 ) ) )

    Identifier.identify( spec )


    EquivalenceDB.processAll( spec )

    println( EquivalenceDB.size() )

    println("\nEquivalence IDs/classes: \n")
    for( a <- 0 until EquivalenceDB.size() ){
      println( UID( a ) +  " -> " +  EquivalenceDB( UID( a ) ).getOrElse( None ) + " , " + EquivalenceDB.getEqClass( UID( a ) ).getOrElse( None ))
    }

    println( EquivalenceDB.getEx( EID( 0 ) ) )

    EquivalenceDB.reset()
    Identifier.reset()

  }

  test( "Test operator DB" ){

    EquivalenceDB.reset()
    Identifier.reset()

    val a = NameEx( "a" )

    val spec = new TlaSpec( "attributes",
      List(
        TlaOperDecl( "A1", List( ), a ),
        TlaOperDecl( "A2", List( ), a )
      )
    )

    Identifier.identify( spec )

    EquivalenceDB.processAll( spec )

    val eid1 = EquivalenceDB( UID( 0 ) )
    val eid2 = EquivalenceDB( UID( 1 ) )

    println( OperatorDB.size() )
    println( OperatorDB( eid1.get ) )
    println( OperatorDB( eid2.get ) )

    EquivalenceDB.reset()
    Identifier.reset()

  }

}
