package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}
import at.forsyte.apalache.tla.lir.plugins.{BasicSubstitutions, Identifier, OperatorDB, OperatorSubstitution}
import at.forsyte.apalache.tla.lir.db.EquivalenceDB
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
  val specRec =
    new TlaSpec(
      "Recursive arity1",
      List(
        TlaOperDecl(
          "Op",
          List( SimpleFormalParam( "x" ) ),
          OperEx(
            TlaControlOper.ifThenElse,
            OperEx(
              TlaOper.eq,
              NameEx( "x" ),
              ValEx( TlaInt( 0 ) )
            ),
            ValEx( TlaInt( 0 ) ),
            OperEx(
              TlaArithOper.plus,
              ValEx( TlaInt( 1 ) ),
              OperEx(
                TlaOper.apply,
                NameEx( "Op" ),
                OperEx(
                  TlaArithOper.minus,
                  NameEx( "x" ),
                  ValEx( TlaInt( 1 ) )
                )
              )
            )
          )
        )
      )
    )

  val ABody =
    OperEx(
      TlaArithOper.plus,
      NameEx( "x" ),
      ValEx( TlaInt( 1 ) )
    )
  val plusOne =
    new TlaOperDecl(
      "A",
      List(SimpleFormalParam( "x" )),
      ABody
    )

  val emc2 =
    new TlaOperDecl(
      "Esub",
      List(),
      OperEx(
        TlaArithOper.mult,
        NameEx( "m" ),
        OperEx(
          TlaArithOper.exp,
          NameEx( "c" ),
          ValEx( TlaInt( 2 ) )
        )
      )
    )

  val importantTheorem =
    new TlaOperDecl(
      "thrm",
      List(),
      OperEx(
        TlaBoolOper.and,
//        OperEx(
//          TlaOper.eq,
//          NameEx( "E" ),
//          NameEx( "Esub" )
//        ),
        OperEx(
          TlaOper.eq,
          ValEx( TlaInt( 1 ) ),
          OperEx(
            TlaOper.apply,
            NameEx( "A" ),
            ValEx( TlaInt( 0 ) )
          )
        )
      )
    )

  val specOper = new TlaSpec(
    "Replace operators",
    List( plusOne, /*emc2,*/ importantTheorem)
  )




  ignore("Check ID allocation for basic operator") {

    val spec = specSnd

    Identifier.reset()

    println( "\nspecSnd before: \n" )
    show( spec )

    println( "\nspecSnd after: \n" )
    Identifier.identify( spec )
    show( spec )

    Identifier.reset()


  }

  ignore("Check basic substitution") {

    val spec = specSum

    Identifier.reset()

    println( "\nspecSum before:\n" )
    show( spec )

    println( "\nspecSum after: \n" )
    val after = BasicSubstitutions.sub( spec )
    Identifier.identify( after )
    show( after )

    val spec2 = specBool

    println( "\nspecBool before:\n" )
    show( spec2 )

    println( "\nspecBool after: \n" )
    val after2 =  BasicSubstitutions.sub( spec2 )
    Identifier.identify( after2 )
    show( after2 )

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

  ignore( "Test operator DB" ){

    Identifier.reset()
    EquivalenceDB.reset()
    OperatorDB.reset()

    val spec = specSnd

    Identifier.identify( spec )

    Identifier.print()

    EquivalenceDB.processAll( spec )

    OperatorSubstitution.extract( spec )


    Identifier.print()
    EquivalenceDB.print()
    OperatorDB.print()

    OperatorDB.reset()
    EquivalenceDB.reset()
    Identifier.reset()

  }

  ignore( "Test operator DB recursion check" ){

    OperatorDB.reset()
    EquivalenceDB.reset()
    Identifier.reset()

    val spec = specRec
    val spec2 = specSum

    Identifier.identify( spec )
    EquivalenceDB.processAll( spec )
    OperatorSubstitution.extract( spec )

    Identifier.identify( spec2 )
    EquivalenceDB.processAll( spec2 )
    OperatorSubstitution.extract( spec2 )

//    Identifier.print()
//    EquivalenceDB.print()
//    OperatorDB.print()

    assert( OperatorDB.isRecursive( EquivalenceDB.getFromEx( NameEx( "Op" ) ) ) == Some(true) )
    assert( OperatorDB.isRecursive( EquivalenceDB.getFromEx( NameEx( "" ) ) ) == Some(false) )
    assert( OperatorDB.isRecursive( EID( -1 ) ) == None )


    OperatorDB.reset()
    EquivalenceDB.reset()
    Identifier.reset()


  }

  test( "Test operator DB substitution" ) {

    OperatorDB.reset()
    EquivalenceDB.reset()
    Identifier.reset()

    val spec = specOper



    Identifier.identify( spec )
    EquivalenceDB.processAll( spec )
    OperatorSubstitution.extract( spec )

//    Identifier.print()
//    EquivalenceDB.print()
//    OperatorDB.print()

//    val retSpc = OperatorSubstitution.substituteOper( spec )

    val ex = OperEx( TlaOper.apply, NameEx("A"), ValEx( TlaInt(0) ) )
    Identifier.identify( ex )
    EquivalenceDB( ex.ID )

    println( ex )

    println( OperatorSubstitution.applyReplace( ex ) )

    println("--------------------------")

//    val newex = OperatorSubstitution.applyReplace(
//      Identifier.identify( ex  )
//    )
//    println( ex )

//    println( retSpc.declarations.reverse.head )

    OperatorDB.reset()
    EquivalenceDB.reset()
    Identifier.reset()

  }

  }
