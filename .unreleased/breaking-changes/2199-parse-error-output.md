The format of parsing error outputs has been changed. Parsing error messages
that used to be prefixed with `Error by TLA+ parser` are now prefixed with
`Parsing error` and error messages that used to begin with `Syntax error in
annotation:` will now also include the `Parsing error` prefix. This is being
recorded as a breaking change since it could break scripts that rely on parsing
stdout. (See #2204 and #2242.)
