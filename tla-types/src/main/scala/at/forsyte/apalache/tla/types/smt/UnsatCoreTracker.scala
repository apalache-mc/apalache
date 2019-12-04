package at.forsyte.apalache.tla.types.smt

import at.forsyte.apalache.tla.types.Names
import com.microsoft.z3.{BoolExpr, Context}

/** Keeps track of which SMT labels (BoolExpr) represent which constraints */
class UnsatCoreTracker( private val ctx: Context ) {
  private var idx : Int = 0
  private var map : Map[BoolExpr, BoolExpr] = Map.empty

  def add( ex: BoolExpr ) : BoolExpr = {
    val label = ctx.mkBoolConst( s"${Names.labelSymb}$idx" )
    idx += 1
    map += label -> ex
    label
  }

  def recover( ex: BoolExpr ) : BoolExpr = map(ex)

}
