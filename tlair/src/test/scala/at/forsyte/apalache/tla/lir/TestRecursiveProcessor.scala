package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TestRecursiveProcessor extends FunSuite with TestingPredefs {
  test("Proper termination"){

    def terminationTest(p_ex: TlaEx) : Boolean = p_ex match {
      case NameEx(n) => true
      case _ => false
    }

    def terminalFun(p_ex: TlaEx): Unit = p_ex match {
      case NameEx(n) => println(n)
      case _ => ()
    }

    def nonterminalFun(p_ex: TlaEx): Unit = println(p_ex + " is not a NameEx")

    def unification(p_ex: TlaEx, p_children: Traversable[Unit]): Unit = ()

    val ex = tla.primeInSingleton( n_x, n_S )

    val fun = RecursiveProcessor.computeFromTlaEx( terminationTest, terminalFun, nonterminalFun, unification)

    fun(ex)

    fun(trueEx)
  }
}