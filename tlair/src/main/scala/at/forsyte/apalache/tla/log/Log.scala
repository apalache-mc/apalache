package at.forsyte.apalache.tla.log

import java.util.Calendar

/**
  * @deprecated use slf4j and scala-logging instead
  */
object Log {
  abstract class errorLevel{
    val m_priority: Int
    def <( lhs: errorLevel, rhs: errorLevel ) = lhs.m_priority < rhs.m_priority
  }
  case class errLevelLOG() extends errorLevel{
    val m_priority = 0
  }
  case class errLevelWARNING() extends errorLevel{
    val m_priority = 10
  }
  case class errLevelERROR() extends errorLevel{
    val m_priority = 1000
  }

  var m_awake: Boolean = false
  var m_initTime: String = ""

  def start(): Unit = {
    if( m_awake ) return
    val now = Calendar.getInstance().getTime

    print( now )
    m_awake = true

  }

  var logpath: String = "."
  val logName = ".log"

  def <<( mesage: Any ) = {

  }



}
