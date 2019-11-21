package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper.FixedArity
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaInt, TlaTrue}

// Igor@02.11.2019: why are TestingPredefs located in src/main?
// TODO: move TestingPredefs into src/test
trait TestingPredefs {
  implicit def name( p_s : String ) : NameEx = NameEx( p_s )
  implicit def value( p_n : Int  ) : ValEx = ValEx( TlaInt( p_n ) )
  implicit def sfp( p_s : String ) : SimpleFormalParam = SimpleFormalParam( p_s )
  implicit def ofp( p_pair : (String, Int) ) : OperFormalParam =
    OperFormalParam( p_pair._1, p_pair._2 )

  def n_a : NameEx = "a"
  def n_b : NameEx = "b"
  def n_c : NameEx = "c"
  def n_d : NameEx = "d"
  def n_e : NameEx = "e"
  def n_f : NameEx = "f"
  def n_g : NameEx = "g"

  def n_p : NameEx = "p"
  def n_q : NameEx = "q"
  def n_r : NameEx = "r"
  def n_s : NameEx = "s"
  def n_t : NameEx = "t"

  def n_A : NameEx = "A"
  def n_B : NameEx = "B"
  def n_S : NameEx = "S"
  def n_T : NameEx = "T"
  def n_P : NameEx = "P"
  def n_Q : NameEx = "Q"

  def n_x : NameEx = "x"
  def n_y : NameEx = "y"
  def n_z : NameEx = "z"

  def trueEx  : ValEx = ValEx( TlaTrue )
  def falseEx : ValEx = ValEx( TlaFalse )

  def arr   : Array[TlaEx] = Array( n_a, n_b, n_c, n_d, n_e, n_f, n_g )
  def arr_s : Seq[TlaEx]   = arr.toSeq

  def seq( n : Int, nSkip : Int = 0 ) : Seq[TlaEx] = arr.slice( nSkip, n + nSkip ).toSeq ++ Seq.fill( n - arr.length )( n_x )

  def x_in_S : OperEx = Builder.in( "x", "S" )

  def printlns( p_ss : String* )
              ( implicit p_surround : Boolean = true ) : Unit =
    println( (if ( p_surround ) p_ss.map( "\"%s\"".format( _ ) ) else p_ss).mkString( "\n" ) )

  def printsep() : Unit = println( "\n%s\n".format( Seq.fill( 20 )( "-" ).mkString ) )

  def noOp() : Unit = {}

  def prePostTest( f: => Unit, pre : () => Unit = noOp, post: () => Unit = noOp ) : Unit = {
    pre()
    f
    post()
  }

}
