# Apalache Documentation

The Apalache documentation is written in markdown files in the [./src](./src)
directory and compiled using [mdbook](https://github.com/rust-lang/mdBook).

To view the documentation, visit https://apalache.informal.systems/docs/ .

## Building and previewing the documentation

To build the documentation into [../target/docs](../target/docs), run

```sh
mdbook build
```

To start a server that will present a live updated view of the book while you
edit, run

```sh
mdbook serve
```

## Notes on writing the documentation

### Emoji

We have hacked together support for _most_ GitHub emoji names in the docs. So,
if you write

```markdown
:duck:
```

then, after compiling in our CI during deployment, it will render as

```markdown
🦆
```

Our CI uses the [emojitsu](https://github.com/shonfeder/emojitsu#emojitsu) CLI
utility. You can also use this tool to lookup the name for an emoji if you have
the unicode on hand or to see how a name will render.

Note that GitHub cheats in it's rendering: it replaces emojinames with pngs, and
includes some emojis which are not supported by the unicode standard. We don't
stand for this standardless stuff at the moment, because it would be too tedious
to implement.

### The Table of Contents

The [./src/SUMMARY.md](./src/SUMMARY.md) specifies the table of contents shown
in the sidebar of the documentation. Any top-level chapters must be linked from
there.

Each chapter must link a file: internal links to anchors within files do not
work. There is an [open issue](https://github.com/rust-lang/mdBook/issues/167)
to fix this behavior.

## Internal documentation

Design notes and memos that are part of the documentation of our design process
or for reference by developers are collected in [./internal](./internal).
