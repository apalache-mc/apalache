package at.forsyte.apalache.tla.lir

object RecursiveProcessor {
  def compute[T1, T2](
                       p_terminationCheck : T1 => Boolean,
                       p_terminalExFun : T1 => T2,
                       p_nonTerminalExFun : T1 => T2,
                       p_hasChildren : T1 => Boolean,
                       p_getChildren : T1 => Traversable[T1],
                       p_childUnification : (T1, Traversable[T2]) => T2
                     )(
                       p_ex : T1
                     ) : T2 =
    if ( p_terminationCheck( p_ex ) )
      p_terminalExFun( p_ex )
    else if ( p_hasChildren( p_ex ) ) {
      val childVals : Traversable[T2] =
        p_getChildren( p_ex ) map compute(
          p_terminationCheck,
          p_terminalExFun,
          p_nonTerminalExFun,
          p_hasChildren,
          p_getChildren,
          p_childUnification
        )
      p_childUnification( p_ex, childVals )
    }
    else p_nonTerminalExFun( p_ex )

  def computeFromTlaEx[T](
                           p_terminationCheck : TlaEx => Boolean,
                           p_terminalExFun : TlaEx => T,
                           p_nonTerminalExFun : TlaEx => T,
                           p_childUnification : (TlaEx, Traversable[T]) => T
                         ) : TlaEx => T =
    compute[TlaEx, T](
      p_terminationCheck,
      p_terminalExFun,
      p_nonTerminalExFun,
      _.isInstanceOf[OperEx],
      _.asInstanceOf[OperEx].args,
      p_childUnification
    )

  def transformTlaEx(
                      p_terminationCheck : TlaEx => Boolean,
                      p_terminalExFun : TlaEx => TlaEx,
                      p_nonTerminalExFun : TlaEx=> TlaEx
                    ) : TlaEx => TlaEx =
    computeFromTlaEx[TlaEx](
      p_terminationCheck,
      p_terminalExFun,
      p_nonTerminalExFun,
      (ex,children) => ex match {
        case OperEx(oper, args@_*) => if (args == children) ex else OperEx(oper, children.toSeq: _*)
        case _ => ex // never be called by construction, but makes warnings go away
      }
    )
}
