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

  def printState(pretty: PrettyWriter, state: State) = {
    val body =
      if (state.isEmpty) {
        ValEx(TlaBool(true))
      } else {
        val keyVals = state.toList.sortBy(_._1)
          .map(p => OperEx(TlaOper.eq, NameEx(p._1), p._2))
        OperEx(TlaBoolOper.and, keyVals :_*)
      }
    pretty.write(body)
  }
}

class TlaCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  def write(notInvariant: NotInvariant, init: State, nextStates: List[NextState] ) : Unit = {
    val pretty = new PrettyWriter(writer)

    def printNextState(prefix: String, name: String, state: State) = {
      writer.print(
        s"""$prefix
           |
           |$name == """.stripMargin)
      printState(pretty, state)
      writer.println("\n")
    }

    var i = 0
    printNextState(
      "(* Initial state *)",
      s"State$i",
      init)
    for (nextState <- nextStates) {
      i += 1
      printNextState(
        s"(* Transition ${nextState._1} to State$i *)",
        s"State$i",
        nextState._2)
    }
    writer.print(
      s"""(* The following formula holds true in State$i and violates the invariant *)
         |
         |""".stripMargin)
    pretty.write(TlaOperDecl("InvariantViolation", List(), notInvariant))
    writer.println("\n")
  }
}


class TlcCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {

  def write(notInvariant: NotInvariant, init: State, nextStates: List[NextState]): Unit = {
    val pretty = new PrettyWriter(writer)

    def printNextState(prefix: String, state: State) = {
      writer.println(
        s"""@!@!@STARTMSG 2217:4 @!@!@
           |$prefix""".stripMargin)
      printState(pretty, state)
      writer.println(
        """|
           |
           |@!@!@ENDMSG 2217 @!@!@""".stripMargin)
    }

    writer.print(
      s"""@!@!@STARTMSG 2110:1 @!@!@
         |Invariant is violated.
         |@!@!@ENDMSG 2110 @!@!@
         |@!@!@STARTMSG 2121:1 @!@!@
         |The behavior up to this point is:
         |@!@!@ENDMSG 2121 @!@!@
         |""".stripMargin)

    var i = 1
    printNextState(
      s"$i: <Initial predicate>",
      init)
    for (nextState <- nextStates) {
      i += 1
      printNextState(
        s"$i: <Next>",
        nextState._2)
    }
  }
}
