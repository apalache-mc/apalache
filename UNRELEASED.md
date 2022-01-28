<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Features

         * Change description, see #123

        ### Bug fixes

         * Some bug fix, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->
### Breaking changes

- Switched build system from maven to sbt (note, will only cause breakage in
  pipelines that build from source), See #1234.

### Features

 * Completely remove TlcOper and replace it with a custom TLA+ module, see #1253

### Bug fixes

 * Fix the semantics of @@ by using the TLC definition, see #1182, #951, #1234
 * Fix unexpected polymorphism, see #1262
  
