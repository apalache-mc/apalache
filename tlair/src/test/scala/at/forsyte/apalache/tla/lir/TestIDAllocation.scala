package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.plugins._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.mutable.Set

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
                                             IntEx( 1 ),
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
    OperEx( TlaArithOper.plus, IntEx( 4 ), IntEx( 0 ) ),
    OperEx( TlaArithOper.plus, IntEx( 2 ), IntEx( 2 ) )
  )

  val redundantbool = OperEx( TlaOper.eq,
    OperEx( TlaBoolOper.and, NameEx( "x" ), ValEx( TlaTrue ) ),
    OperEx( TlaBoolOper.or, ValEx( TlaFalse ), NameEx( "x" ) )
  )


  val specSnd = new TlaSpec("Test spec.", List(SndNewValue))
  val specSum = new TlaSpec( "someSum", List( TlaOperDecl( "sum", List( ), sum ) ) )
  val specBool = new TlaSpec( "boolSimplification", List( TlaOperDecl( "redundant bool", List( ), redundantbool ) ) )
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
              IntEx( 0 )
            ),
            IntEx( 0 ),
            OperEx(
              TlaArithOper.plus,
              IntEx( 1 ),
              OperEx(
                TlaOper.apply,
                NameEx( "Op" ),
                OperEx(
                  TlaArithOper.minus,
                  NameEx( "x" ),
                  IntEx( 1 )
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
      IntEx( 1 )
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
          IntEx( 2 )
        )
      )
    )

  val importantTheorem =
    new TlaOperDecl(
      "thrm",
      List(),
//      OperEx(
//        TlaBoolOper.and,
//        OperEx(
//          TlaOper.eq,
//          NameEx( "E" ),
//          NameEx( "Esub" )
//        ),
        OperEx(
          TlaOper.eq,
          OperEx(
            TlaArithOper.minus,
            IntEx( 2 ),
            IntEx( 1 )
          ),
          OperEx(
            TlaArithOper.plus,
            OperEx(
              TlaOper.apply,
              NameEx( "A" ),
              IntEx( 0 )
            ),
            IntEx( 0 )
          )
        )
//      )
    )

  val specOper = new TlaSpec(
    "Replace operators",
    List( plusOne, /*emc2,*/ importantTheorem)
  )

  def sterileRun( f: () => Unit ): Unit ={
    f()
  }

  def printSpec( spec:TlaSpec ): Unit ={
    println("\n" + spec.name + ":\n")
    spec.declarations.foreach( println )
  }



  }
