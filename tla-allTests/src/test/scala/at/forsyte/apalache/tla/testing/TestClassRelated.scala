package at.forsyte.apalache.tla.testing

import at.forsyte.apalache.tla.lir.plugins.types._

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Created by jkukovec on 4/12/17.
  */
@RunWith(classOf[JUnitRunner])
class TestClassRelated extends FunSuite {

  def checkSelfConsistency( arr: Array[ConstMemCell] ) : Boolean = arr.forall( x => x== x && !(x < x) )
  def checkSelf( arr: Array[ConstMemCell] ) : Boolean = {
    arr.zipWithIndex.forall(
                            pa =>
                            pa._1 == pa._1
                            &&
                            !( pa._1 < pa._1 )
                            &&
                            ( (pa._2 + 1) until arr.length ).forall(
                                                                 i =>
                                                                 ( pa._1 < arr(i) || pa._1 == arr(i) )
                                                                 &&
                                                                 !( arr(i) < pa._1 )
                                                                )
                           )
  }

  test( "Check equality and TotalOrder" ) {
    val trueCell = BoolCell(true)
    val falseCell = BoolCell(false)

    val boolCells : Array[ConstMemCell] = Array( falseCell, trueCell )

    assert( checkSelf(boolCells) )

    val intCell1 = IntCell( -123 )
    val intCell2 = IntCell( 0 )
    val intCell3 = IntCell( 42 )
    val intCell4 = IntCell( Int.MaxValue )

    val intCells : Array[ConstMemCell] = Array( intCell1, intCell2, intCell3, intCell4)

    assert( checkSelf(intCells) )

    val strCell1 = StrCell( "a" )
    val strCell2 = StrCell( "aa" )
    val strCell3 = StrCell( "abc" )
    val strCell4 = StrCell( "b" )
    val strCell5 = StrCell( "cba" )

    val strCells : Array[ConstMemCell] = Array( strCell1,strCell2, strCell3,strCell4,strCell5)

    assert( checkSelf(strCells) )

    val nullSetCell = SetCell()
    val setCell1 = SetCell(trueCell, falseCell)
    val setCell2 = SetCell(falseCell,falseCell,falseCell,trueCell)
    val setCell3 = SetCell( nullSetCell )
    val setCell4 = SetCell( nullSetCell, trueCell, intCell1, setCell2)

    val setCells : Array[ConstMemCell] = Array( nullSetCell, setCell3, setCell2, setCell1, setCell4)

    assert( setCell1 == setCell2 )
    assert( checkSelf(setCells) )


    val mixCells1 : Array[ConstMemCell] = Array( falseCell, intCell2, intCell3, strCell2 ,nullSetCell, setCell3 )
    val mixCells2 : Array[ConstMemCell] = Array( strCell2, falseCell, intCell2, intCell3 ,nullSetCell, setCell3 )

    assert( checkSelf(mixCells1) && !checkSelf(mixCells2) )

  }

}
