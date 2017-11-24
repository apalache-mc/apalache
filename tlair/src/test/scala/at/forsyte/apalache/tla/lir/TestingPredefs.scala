package at.forsyte.apalache.tla.lir

trait TestingPredefs {
  implicit def name( p_s : String ) : NameEx = NameEx( p_s )

  val n_a : NameEx = "a"
  val n_b : NameEx = "b"
  val n_c : NameEx = "c"
  val n_d : NameEx = "d"
  val n_e : NameEx = "e"
  val n_f : NameEx = "f"
  val n_g : NameEx = "g"

  val n_p : NameEx = "p"
  val n_q : NameEx = "q"
  val n_r : NameEx = "r"

  val n_A : NameEx = "A"
  val n_S : NameEx = "S"
  val n_T : NameEx = "T"
  val n_P : NameEx = "P"
  val n_Q : NameEx = "Q"

  val n_x : NameEx = "x"

  val arr   : Array[TlaEx] = Array( n_a, n_b, n_c, n_d, n_e, n_f, n_g )
  val arr_s : Seq[TlaEx]   = arr.toSeq

  def seq( n : Int ) : Seq[TlaEx] = arr.slice( 0, n ).toSeq ++ Seq.fill( n - arr.length )( n_x )

  val x_in_S : OperEx = Builder.in( "x", "S" )

  def printlns( p_ss : String* )
              ( implicit p_surround : Boolean = true ) : Unit =
    println( (if ( p_surround ) p_ss.map( "\"%s\"".format( _ ) ) else p_ss).mkString( "\n" ) )

  def printsep() : Unit = println( "\n%s\n".format( Seq.fill( 20 )( "-" ).mkString ) )

}
