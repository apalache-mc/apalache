package at.forsyte.apalache.tla.bmcmt.passes

/**
  * An analysis pass parameterized by its input and output.
  *
  * @author Igor Konnov
  */
trait Pass[InT, OutT] {
  /**
    * The name of the pass
    * @return the name associated with the pass
    */
  def name: String

  /**
    * Run the pass
    * @return true, if the pass was successful
    */
  def run(): Boolean

  /**
    * Get the input to the pass.
    * @return the input, possibly None
    */
  def getInput: Option[InT]

  /**
    * Set the input to the pass.
    * @param in the input
    */
  def setInput(in: InT)

  /**
    * Get the output of the pass.
    * @return the output
    */
  def getOutput: Option[OutT]
}
