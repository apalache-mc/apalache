------------------- MODULE CommentedTypeAnnotation -----------------------

(* Used as regression test for https://github.com/apalache-mc/apalache/issues/2163 *)

CONSTANT
  \* @type: Set({
  \*   // a comment
  \*   x : Int
  \*});
  v,
  \* @type: {
  \*   // another comment
  \*   x : Int,
  \*   // a third comment
  \*   y : Seq(Int)
  \*};
  y

============================================================
