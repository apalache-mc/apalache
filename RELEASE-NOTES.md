## 0.8.1

### Bug fixes

 * critical bugfix in unique renaming, #429

### Features

 * opt-in for statistics collection (shared with TLC and TLA+ Toolbox), see #288
 
### Architecture
 
 * new layer of TransitionExecutor (TRex), see `at.forsyte.apalache.tla.bmcmt.trex.*`

### Documentation

 * Compile the manuals into [a static
  site](http://informalsystems.github.io/apalache/docs/) using
  [mdBook](https://github.com/rust-lang/mdBook), see #400 
 * Description of top-level user operators, see #419
 * ADR003: [Architecture of TransitionExecutor](./docs/internal/adr/003adr-trex.md) 
