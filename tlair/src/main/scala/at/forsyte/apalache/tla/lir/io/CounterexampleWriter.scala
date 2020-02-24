package at.forsyte.apalache.tla.lir.io

import java.io.PrintWriter

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
/**
 * A printer for counterexamples, in various formats: TLA+ , as TLC output, ...
 *
 * @author Andrey Kuprianov
 */
abstract class CounterexampleWriter {
  // Print out invariant violation
  def write(notInvariant: NotInvariant, init: State, nextStates: List[NextState] ) : Unit

  def printState(pretty: PrettyWriter, name: String, state: State) = {
    val body =
      if (state.isEmpty) {
        ValEx(TlaBool(true))
      } else {
        val keyVals = state.toList.sortBy(_._1)
          .map(p => OperEx(TlaOper.eq, NameEx(p._1), p._2))
        OperEx(TlaBoolOper.and, keyVals :_*)
      }
    pretty.write(TlaOperDecl(name, List(), body))
  }
}

class TlaCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  def write(notInvariant: NotInvariant, init: State, nextStates: List[NextState] ) : Unit = {
    val pretty = new PrettyWriter(writer)

    def printNextState(name: String, nextState: NextState) = {
      writer.println(
        s"""(* Transition ${nextState._1} to $name *)
           |""".stripMargin)
      printState(pretty, name, nextState._2)
      writer.println("\n")
    }

    var i = 0
    writer.print(
      """(* Initial state *)"
        |
        |""".stripMargin)
    printState(pretty, s"State$i", init)
    writer.println("\n")
    for (st <- nextStates) {
      i += 1
      printNextState(s"State$i", st)
    }
    writer.println(
      s"""(* The following formula holds true in State$i and violates the invariant *)
         |""".stripMargin)
    pretty.write(TlaOperDecl("InvariantViolation", List(), notInvariant))
    writer.println("\n")
  }
}
