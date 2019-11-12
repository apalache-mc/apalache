package at.forsyte.apalache.tla.types.smt

import com.microsoft.z3._

/**
  * We define wrappers around the z3 data structures, which allow us mimic the functions sizeOf,
  * hasIndex/atIndex and hasField/atField as Scala Int => Int or (Int,Int) => Option[Expr] functions.
  *
  * See TypeReconstructor
  */
object FunWrappers {

  sealed case class SizeFunWrapper( ctx : Context, m : Model, decl : FuncDecl ) {
    def apply( arg : Int ) : Int = {
      // To evaluate sizeOf(arg), we construct the expression
      // ( sizeOf i )
      // and evaluate it within the model
      val appExpr = ctx.mkApp( decl, ctx.mkInt( arg ) )
      val r = m.eval( appExpr, false )
      // Sanity check + cast
      assert( r.isIntNum )
      r.asInstanceOf[IntNum].getInt
    }
  }

  // has-at functions differ from sizeOf, in that we only care about the at-value, if the has-value is true
  sealed case class HasAtFunWrapper(
                                     ctx : Context,
                                     m : Model,
                                     hasDecl : FuncDecl,
                                     atDecl : FuncDecl
                                   ) {
    def apply( i : Int, j : Int ) : Option[Expr] = {
      // First, we construct the expression
      // ( hasIndex i j ) (resp. ( hasField i j ))
      // and evaluate it in the model
      val hasAppExpr = ctx.mkApp( hasDecl, ctx.mkInt( i ), ctx.mkInt( j ) )
      val hasBool = m.eval( hasAppExpr, false )
      // Sanity check + cast
      assert( hasBool.isBool )
      val hasBoolVal = hasBool.asInstanceOf[BoolExpr].getBoolValue
      // If the value is either false or undefined, we return None
      hasBoolVal.toInt match {
        case 1 =>
          // Otherwise, we construct
          // ( atIndex i j ) (resp. ( atField i j ))
          // and evaluate it.
          val atAppExpr = ctx.mkApp( atDecl, ctx.mkInt( i ), ctx.mkInt( j ) )
          val r = m.eval( atAppExpr, false )
          // We do not cast this value to anything, because handling custom SMT datatypes is
          // most easily done by string-matching
          Some( r )
        case _ => None
      }
    }
  }
}
