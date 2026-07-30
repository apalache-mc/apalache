Configuration files now use strict JSON and the canonical `.apalache.json` /
`$HOME/.tlaplus/apalache.json` names. HOCON is no longer supported. Old application configuration filenames ending in
`.cfg` are rejected, even when they contain valid JSON; rename them before upgrading. Keys formerly nested under
`common` now belong at the JSON root. TLC configuration files passed with
`--config` may still use `.cfg`. The former `input.source` and `output.output`
fields are now the top-level `source` and `output` fields.
