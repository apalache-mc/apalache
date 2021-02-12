package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs.untyped

/**
 * Created by jkukovec on 11/30/16.
 */

@RunWith(classOf[JUnitRunner])
class TestIDAllocation extends FunSuite {

  def show(thisSpec: TlaSpec) = {
    thisSpec.declarations.foreach(x =>
      x match {
        case TlaOperDecl(_, _, ex) => println(ex)
      }
    )
  }

  /**
   * SndNewValue(d) == /\ sAck      = sBit
   * /\ sent'     = d
   * /\ sBit'     = 1 - sBit
   * /\ msgQ'     = Append( msgQ, << sBit', d >> )
   * /\ UNCHANGED   << ackQ, sAck, rBit, rcvd >>
   */
  val SndNewValue =
    new TlaOperDecl("SndNewValue", List(SimpleFormalParam("d")),
        OperEx(
            TlaBoolOper.and,
            OperEx(TlaOper.eq, NameEx("sAck"), NameEx("sBit")),
            OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("sent")), NameEx("d")),
            OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("sBit")),
                OperEx(TlaArithOper.minus, ValEx(TlaInt(1)), NameEx("sBit"))),
            OperEx(TlaOper.eq, OperEx(TlaActionOper.prime, NameEx("msgQ")),
                OperEx(TlaSeqOper.append, NameEx("msgQ"),
                    OperEx(TlaFunOper.tuple, OperEx(TlaActionOper.prime, NameEx("sBit")), NameEx("d")))),
            OperEx(TlaActionOper.unchanged,
                OperEx(TlaFunOper.tuple, NameEx("ackQ"), NameEx("sAck"), NameEx("rBit"), NameEx("rcvd")))
        ))

  val sum = OperEx(TlaOper.eq, OperEx(TlaArithOper.plus, ValEx(TlaInt(4)), ValEx(TlaInt(0))),
      OperEx(TlaArithOper.plus, ValEx(TlaInt(2)), ValEx(TlaInt(2))))

  val redundantbool = OperEx(TlaOper.eq, OperEx(TlaBoolOper.and, NameEx("x"), ValEx(TlaBool(true))),
      OperEx(TlaBoolOper.or, ValEx(TlaBool(false)), NameEx("x")))

  val specSnd = new TlaSpec("Test spec.", List(SndNewValue))
  val specSum = new TlaSpec("someSum", List(TlaOperDecl("sum", List(), sum)))
  val specBool = new TlaSpec("boolSimplification", List(TlaOperDecl("redundant bool", List(), redundantbool)))
  val specRec =
    new TlaSpec(
        "Recursive arity1",
        List(
            TlaOperDecl(
                "Op",
                List(SimpleFormalParam("x")),
                OperEx(
                    TlaControlOper.ifThenElse,
                    OperEx(
                        TlaOper.eq,
                        NameEx("x"),
                        ValEx(TlaInt(0))
                    ),
                    ValEx(TlaInt(0)),
                    OperEx(
                        TlaArithOper.plus,
                        ValEx(TlaInt(1)),
                        OperEx(
                            TlaOper.apply,
                            NameEx("Op"),
                            OperEx(
                                TlaArithOper.minus,
                                NameEx("x"),
                                ValEx(TlaInt(1))
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
        NameEx("x"),
        ValEx(TlaInt(1))
    )
  val plusOne =
    new TlaOperDecl(
        "A",
        List(SimpleFormalParam("x")),
        ABody
    )

  val emc2 =
    new TlaOperDecl(
        "Esub",
        List(),
        OperEx(
            TlaArithOper.mult,
            NameEx("m"),
            OperEx(
                TlaArithOper.exp,
                NameEx("c"),
                ValEx(TlaInt(2))
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
                ValEx(TlaInt(2)),
                ValEx(TlaInt(1))
            ),
            OperEx(
                TlaArithOper.plus,
                OperEx(
                    TlaOper.apply,
                    NameEx("A"),
                    ValEx(TlaInt(0))
                ),
                ValEx(TlaInt(0))
            )
        )
//      )
    )

  val specOper = new TlaSpec(
      "Replace operators",
      List(plusOne, /*emc2,*/ importantTheorem)
  )

  def sterileRun(f: () => Unit): Unit = {
    f()
  }

  def printSpec(spec: TlaSpec): Unit = {
    println("\n" + spec.name + ":\n")
    spec.declarations.foreach(println)
  }

}
