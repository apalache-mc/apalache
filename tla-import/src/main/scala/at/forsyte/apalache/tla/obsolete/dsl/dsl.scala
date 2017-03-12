import scala.collection.mutable

package at.forsyte.apalache.tla.obsolete.dsl {


/**
 * Domain-specific classes and objects that allow one to write TLA+ code directly.
 */

abstract class TlaExpr

case class TlaInt(v: Int) extends TlaExpr

case class TlaStr(v: String) extends TlaExpr


abstract class TlaSym

case class TlaVar(name: String)

case class TlaConst(name: String)

case class TlaOper(sname: Symbol, sargs: List[Symbol], var body: Option[TlaExpr]) {
  def ARGS(args: Symbol*) = new TlaOper(sname, args.toList, None)

  def DEF(e: TlaExpr) = {
    body = Some(e)
    this
  }
}

case class TlaInstance(name: String) {
  var subst: List[Tuple2[Symbol, TlaExpr]] = List()

  def WITH(params: Tuple2[Symbol, TlaExpr]*) =
    subst = params.toList
}


class Module(private val builder: Builder, val namesym: Symbol) {
  private val symbols: Map[String, TlaSym] = Map()
  private var assumptions: List[TlaExpr] = List()
  private var imports: List[String] = List()

  def name = namesym.name

  def EXTENDS(mods: Symbol*) =
    for (s <- mods.reverseIterator)
      imports = s.name :: imports

  def CONSTANT(s: Symbol) = symbols + (s.name -> TlaConst(s.name))

  def CONSTANTS(syms: Symbol*) = for (s <- syms) CONSTANT(s)

  def VARIABLE(s: Symbol) = symbols + (s.name -> TlaVar(s.name))

  def VARIABLES(syms: Symbol*) = for (s <- syms) VARIABLE(s)

  def ASSUME(e: TlaExpr) =
    assumptions = e :: assumptions

  def OPER(opsym: Symbol) = {
    val oper = new TlaOper(sname = opsym, sargs = List(), body = None)
    symbols + (opsym.name -> oper)
    oper
  }

  def INSTANCE(opsym: Symbol) = new TlaInstance(opsym.name)
}


class Builder {
  def MODULE(name: Symbol) = new Module(this, name)
}


/**
 * Implicit conversions. Use import Implicit._ to enable the conversions.
 */
object Implicit {
  implicit def intToTlaExpr(i: Int): TlaExpr = TlaInt(i)

  implicit def stringToTlaExpr(s: String): TlaExpr = TlaStr(s)
}

}