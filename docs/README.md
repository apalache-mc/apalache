# Apalache User Manual

The apalache user manual is written in markdown files in the [./src](./src)
directory and compiled using [mdbook](https://github.com/rust-lang/mdBook).

## Building and previewing the documentation

To build the documentation into [../target/docs](../target/docs), run

``` sh
mdbook build
```

To start a server that will present a live updated view of the book while you
edit, run

``` sh
mdbook serve
```

## Notes on writing the documentation

The [./src/SUMMARY.md](./src/SUMMARY.md) specifies the table of contents shown
in the sidebar of the documentation. Any top-level chaptes must be linked from
there.

## Internal documentation

Design notes and memos that are part of the documentation of our design process
or for reference by developers are collected in [./internal](./internal).
