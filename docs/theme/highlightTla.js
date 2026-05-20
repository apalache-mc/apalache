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

(function addApalacheFooter() {
  let content = document.getElementById("mdbook-content");
  if (!content || document.getElementById("apalache-site-footer")) {
    return;
  }

  if (!document.getElementById("apalache-footer-style")) {
    let style = document.createElement("style");
    style.id = "apalache-footer-style";
    style.textContent = [
      ".apalache-site-footer {",
      "  max-width: var(--content-max-width);",
      "  margin: 30px auto 0;",
      "  padding: 18px var(--page-padding) 0;",
      "  border-top: 1px solid var(--table-border-color);",
      "  color: var(--icons);",
      "  font-size: 0.85em;",
      "}",
      ".apalache-site-footer p {",
      "  margin: 0 0 8px;",
      "  line-height: 1.45em;",
      "}"
    ].join("\n");
    document.head.appendChild(style);
  }

  let footer = document.createElement("footer");
  footer.id = "apalache-site-footer";
  footer.className = "apalache-site-footer";
  footer.setAttribute("role", "contentinfo");
  footer.innerHTML = [
    "<p>Copyright &copy; Apalache a Series of LF Projects, LLC</p>",
    "<p>For web site terms of use, trademark policy and other project policies please see ",
    "<a href=\"https://lfprojects.org\">lfprojects.org</a>.</p>"
  ].join("");

  content.appendChild(footer);
})();
