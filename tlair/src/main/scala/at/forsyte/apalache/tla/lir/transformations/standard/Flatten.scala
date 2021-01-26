package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.transformations.{
  TlaExTransformation,
  TransformationTracker
}

object Flatten {
  private def sameOp(op: TlaOper)(ex: TlaEx): Boolean = ex match {
    case OperEx(o, _*) => o == op
    case _             => false
  }

  private def flattenOne(tracker: TransformationTracker): TlaExTransformation =
    tracker.trackEx {
      case ex @ OperEx(TlaBoolOper.and | TlaBoolOper.or, args @ _*) =>
        val hasSameOper = sameOp(ex.oper)(_)
        // We're looking for cases of OperEx( op1, ..., OperEx( op2, ...),... ) where op1 == op2
        val similar = args.exists {
          hasSameOper
        }
        // If there are no direct children with the same operator, do nothing
        if (!similar)
          ex
        else {
          // We want to preserve arg. order
          val newArgs = args flatMap { x =>
            if (hasSameOper(x)) {
              // We steal all children from OperEx subexpressions using the same operator
              x.asInstanceOf[OperEx].args
            } else
              // These arguments stay unchanged
              Seq(x)
          }
          // We know newArgs != args, because similar = true
          OperEx(ex.oper, newArgs: _*)
        }
      case e => e
    }

  /**
    * Returns a transformation that replaces nested conjunction/disjunction with a flattened equivalent.
    *
    * Example:
    * ( a /\ b) /\ c [/\(/\(a,b),c)] -> a /\ b /\ c [/\(a,b,c)]
    */
  def apply(tracker: TransformationTracker): TlaExTransformation =
    tracker.trackEx { ex =>
      val tr = flattenOne(tracker)
      lazy val self = apply(tracker)
      ex match {
        case LetInEx(body, defs @ _*) =>
          // Transform bodies of all op.defs
          def xform: TlaOperDecl => TlaOperDecl =
            tracker.trackOperDecl { d: TlaOperDecl =>
              d.copy(
                body = self(d.body)
              )
            }

          val newDefs = defs map tracker.trackOperDecl { d =>
            d.copy(body = self(d.body))
          }
          val newBody = self(body)
          val retEx =
            if (defs == newDefs && body == newBody) ex
            else LetInEx(newBody, newDefs: _*)
          tr(retEx)

        case OperEx(op, args @ _*) =>
          val newArgs = args map self
          val newEx = if (args == newArgs) ex else OperEx(op, newArgs: _*)
          tr(newEx)

        case _ => tr(ex)
      }
    }
}
