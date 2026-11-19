package org.apalachemc.integration.framework

import org.scalatest.Tag

/** Forces every Tool invocation in an annotated test to run in a fresh JVM. */
object Forked extends Tag("org.apalachemc.integration.framework.Forked")
