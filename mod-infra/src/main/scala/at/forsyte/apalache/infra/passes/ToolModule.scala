package at.forsyte.apalache.infra.passes

import com.google.inject.{AbstractModule}

abstract class ToolModule extends AbstractModule {
  def passes: Seq[Class[_ <: Pass]]
}
