// (Re-)highlight TLA+ code blocks.

/* This is necessary because we include the TLA+ syntax specification and this
 * script via mdbook's `additional-js` config option in `book.toml`. In the
 * rendered HTML, these files are included after mdbook's `book.js`, which kicks
 * off the initial highlighting as soon as it is loaded.
 */
(function highlightTla() {
  // Get all `code.language-tla` blocks and highlight them.
  // Adapted from mdbook: https://github.com/rust-lang/mdBook/blob/6688bd8d7b7cd8da0f5c5f697e9e730880413828/src/theme/book.js#L157-L174
  let code_nodes = Array
    .from(document.querySelectorAll('code.language-tla'))
    // Don't highlight `inline code` blocks in headers.
    .filter(function (node) { return !node.parentElement.classList.contains("header"); });

  code_nodes.forEach(function (block) { hljs.highlightBlock(block); });
})();
