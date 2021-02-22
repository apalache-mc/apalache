package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.TlaToJson

/**
 * A json encoder, using the UJson representation
 */
object TlaToUJson extends TlaToJson[UJsonRep](UJsonFactory)
