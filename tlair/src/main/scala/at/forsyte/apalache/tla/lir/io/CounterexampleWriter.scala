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
}

class TlaCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  def write(notInvariant: NotInvariant, init: State, nextStates: List[NextState] ) : Unit = {
    val pretty = new PrettyWriter(writer)

    def printState(state: State) = {
      val body =
        if (state._2.isEmpty) {
          ValEx(TlaBool(true))
        } else {
          val keyVals = state._2.toList.sortBy(_._1)
            .map(p => OperEx(TlaOper.eq, NameEx(p._1), p._2))
          OperEx(TlaBoolOper.and, keyVals :_*)
        }
      pretty.write(TlaOperDecl(state._1, List(), body))
      writer.println("\n")
    }

    def printNextState(nextState: NextState) = {
      writer.println(s"(* Transition ${nextState._1} to ${nextState._2._1} *)\n")
      printState(nextState._2)
    }

    writer.println("(* Initial state *)\n")
    printState(init)
    nextStates.foreach(printNextState)

    val last = if(nextStates.isEmpty) init else nextStates.last._2
    writer.println(s"(* The following formula holds true in ${last._1} and violates the invariant *)\n")
    pretty.write(TlaOperDecl("InvariantViolation", List(), notInvariant._2))
    writer.println("\n")
  }
}
