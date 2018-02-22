package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.plugins._
import at.forsyte.apalache.tla.lir.db._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.mutable.Set
import Identifiable.IDReallocationError

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


  def clearAll(): Unit ={
    OperatorDB.clear()
    EquivalenceDB.clear()
    UniqueDB.clear()
    OriginDB.clear()
  }

  def sterileRun( f: () => Unit ): Unit ={
    clearAll()
    f()
  }

  def printDBs(): Unit ={
    UniqueDB.print()
    EquivalenceDB.print()
    OperatorDB.print()
    OriginDB.print()
  }

  def printSpec( spec:TlaSpec ): Unit ={
    println("\n" + spec.name + ":\n")
    spec.declarations.foreach( println )
  }


  test("Check ID allocation for basic operator") {

    def idtest() {
      val spec = specSnd.deepCopy()

//      printSpec( spec )

      Identifier.identify( spec )
//      printSpec( spec )

      var existsUnassigned = false
      var nInvoked = 0
      val uidset : Set[UID] = Set()
      def checkForUA( tlaEx: TlaEx ): Unit = {
        if( tlaEx.ID == UID( -1 ) ) existsUnassigned = true
        else{
          nInvoked = nInvoked + 1
          uidset.add( tlaEx.ID )
        }
      }
      SpecHandler.sideeffectWithExFun( spec, checkForUA )

      assert( !existsUnassigned && uidset.size == nInvoked )

    }

    sterileRun( idtest )


  }

  test("Check basic substitution") {

    def bSub() {
      val spec = specSum.deepCopy( )

//      printSpec( spec )
      val after = BasicSubstitutions.sub( spec )
//      Identifier.identify( after )
//      printSpec( after )

      assert(
        after.declarations.size == 1
        &&
        after.declarations.head == TlaOperDecl( "sum", Nil , ValEx( TlaTrue ) )
      )

      val spec2 = specBool.deepCopy()

//      printSpec( spec2 )


      val after2 = BasicSubstitutions.sub( spec2 )
//      Identifier.identify( after2 )
//      printSpec( after2 )

      assert(
        after2.declarations.size == 1
        &&
        after2.declarations.head == TlaOperDecl( "redundant bool", Nil , ValEx( TlaTrue ) )
      )


    }

    sterileRun( bSub )

  }

  test("Check equivalence") {

    def eqCheck() {
      val spec = specSnd.deepCopy()

      Identifier.identify( spec )

//      printSpec( spec )


      EquivalenceDB.processAll( spec )

//      EquivalenceDB.print()

//      println("\nEquivalence IDs/classes: \n")
//      for( a <- 0 until EquivalenceDB.size() ){
//        println( UID( a ) +  " -> " +  EquivalenceDB( UID( a ) ).getOrElse( None ) + " , " + EquivalenceDB.getEqClass( UID( a ) ).getOrElse( None ))
//      }

      var okAll = true

      def okEQC( tlaEx: TlaEx ) : Unit = {
        val eqc = EquivalenceDB.getEqClass( tlaEx )
        okAll = (
                okAll
                &&
                eqc.nonEmpty
                &&
                eqc.get.nonEmpty
                &&
                eqc.get.forall( UniqueDB.get( _ ).contains( tlaEx ) )
                )
      }

      SpecHandler.sideeffectWithExFun( spec, okEQC )

      assert( okAll )


    }
    sterileRun( eqCheck )

  }

  test( "Check attributes" ){

    def checkAtt() {

      val a1 = NameEx( "a" )
      val a2 = NameEx( "a" )

      val spec =
        TlaSpec(
          "attributes",
          List(
            TlaOperDecl( "A1", List( ), a1 ),
            TlaOperDecl( "A2", List( ), a2 )
          )
        )

      try {
        Identifier.identify( spec )

        a1 setID UID( 99 )
        a2 setID UID( 42 )

        assert( false )
      }
      catch {
        case err: IDReallocationError =>
        case _ : Throwable => assert( false )
      }


      EquivalenceDB.processAll( spec )

      assert( EquivalenceDB.size() == 1 )
//
//      println( "\nEquivalence IDs/classes: \n" )
//      for ( a <- 0 until EquivalenceDB.size( ) ) {
//        println( UID( a ) + " -> " + EquivalenceDB( UID( a ) ).getOrElse( None ) + " , " + EquivalenceDB.getEqClass( UID( a ) ).getOrElse( None ) )
//      }

//      println( EquivalenceDB.getEx( EID( 0 ) ) )

    }

    sterileRun( checkAtt )

  }

  test( "Test operator DB" ){

    def operTest(){
      val spec = specSnd.deepCopy()

      Identifier.identify( spec )

//      Identifier.print()

      EquivalenceDB.processAll( spec )

      OperatorSubstitution.extract( spec )

      val operinfo = OperatorDB.get( EquivalenceDB.getRaw( NameEx( "SndNewValue" ) ) )

      assert(
        operinfo.nonEmpty
        &&
        operinfo.get._1.size == 1
        &&
        EquivalenceDB.getEx(operinfo.get._2).contains(
          specSnd.declarations.head.asInstanceOf[TlaOperDecl].body
        )
      )

//      OperatorDB.print()

      //    printDBs()
    }

    sterileRun( operTest )

  }

  test( "Test operator DB recursion check" ){

    def recCheck() {

      val spec = specRec.deepCopy()
      val spec2 = specSum.deepCopy()

      Identifier.identify( spec )
      EquivalenceDB.processAll( spec )
      OperatorSubstitution.extract( spec )

      Identifier.identify( spec2 )
      EquivalenceDB.processAll( spec2 )
      OperatorSubstitution.extract( spec2 )

      assert( OperatorDB.isRecursive( EquivalenceDB.getRaw( NameEx( "Op" ) ) ).contains( true ) )
      assert( OperatorDB.isRecursive( EquivalenceDB.getRaw( NameEx( "sum" ) ) ).contains( false ) )
      assert( OperatorDB.isRecursive( EID( -1 ) ).isEmpty )


    }

    sterileRun( recCheck )


  }

  test( "Test deep copy" ){
    def copytest(): Unit ={
      val spec1 = specSnd.deepCopy()
      val spec2 = spec1
      val spec3 = spec1.deepCopy()


      Identifier.identify( spec1 )
      Identifier.identify( spec2 )
      Identifier.identify( spec3 )

      assert( spec1.identical(spec2) && !spec1.identical(spec3) )

    }

    sterileRun( copytest )
  }

  test( "Test operator DB substitution" ) {

    def subtest() : Unit = {
      val spec = specOper.deepCopy()

      Identifier.identify( spec )
      EquivalenceDB.processAll( spec )
      OperatorSubstitution.extract( spec )

      val retSpc = OperatorSubstitution.substituteOper( spec )

      assert( retSpc.declarations.head == spec.declarations.head )
      assert( retSpc.declarations.reverse.head.isInstanceOf[TlaOperDecl]
        &&
        retSpc.declarations.reverse.head.asInstanceOf[TlaOperDecl].body ==
          OperEx( TlaOper.eq,
            OperEx( TlaArithOper.minus, IntEx( 2 ), IntEx( 1 ) ),
            OperEx( TlaArithOper.plus,
              OperEx( TlaArithOper.plus,
                IntEx( 0 ),
                IntEx( 1 )
              ),
              IntEx( 0 )
            )
          )
      )

      // the origin of 0 + 1 is A(0)
      val UID1 = OriginDB.get( retSpc.declarations
        .reverse.head.asInstanceOf[TlaOperDecl]
        .body.asInstanceOf[OperEx]
        .args.tail.head.asInstanceOf[OperEx].args.head.ID
      )

      val UID2 = spec.declarations
        .reverse.head.asInstanceOf[TlaOperDecl]
        .body.asInstanceOf[OperEx]
        .args.tail.head.asInstanceOf[OperEx].args.head.ID


      assert( UID1.contains( UID2 ) )

       // the 0 in the + 0 has the same ID
      val UID3 = retSpc.declarations
        .reverse.head.asInstanceOf[TlaOperDecl]
        .body.asInstanceOf[OperEx]
        .args.head.asInstanceOf[OperEx].args.tail.head.ID

      val UID4 = spec.declarations
        .reverse.head.asInstanceOf[TlaOperDecl]
        .body.asInstanceOf[OperEx]
        .args.head.asInstanceOf[OperEx].args.tail.head.ID

      assert( UID3 == UID4 )

      // the 2-1 has the same ID and subIDs in both expressions (i.e. is identical)

      assert( retSpc.declarations
        .reverse.head.asInstanceOf[TlaOperDecl]
        .body.asInstanceOf[OperEx]
        .args.tail.head.asInstanceOf[OperEx].args.tail.head.identical(
        spec.declarations
          .reverse.head.asInstanceOf[TlaOperDecl]
          .body.asInstanceOf[OperEx]
          .args.tail.head.asInstanceOf[OperEx].args.tail.head
          )

      )


    }

    sterileRun( subtest )
  }

  /** Jure, 9.11.2017 : Deprecated, Substitutor methods have changed */
//  test( "Test Plugins" ){
//    def plugtest() : Unit = {
//      val spec = specOper.deepCopy()
//      FirstPass.run(spec)
//      EquivalencePlugin.run(spec)
//      Substitutor.run( spec )
//
//      val spec2 = specOper.deepCopy()
//      Identifier.identify( spec2 )
//      EquivalenceDB.processAll( spec2 )
//      OperatorSubstitution.extract( spec2 )
//      val retSpc = OperatorSubstitution.substituteOper( spec2 )
//
//      assert( retSpc == Substitutor.output )
//    }
//
//    sterileRun( plugtest )
//  }

  }
