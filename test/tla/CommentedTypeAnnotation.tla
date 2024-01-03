------------------- MODULE CommentedTypeAnnotation -----------------------

(* Used as regression test for https://github.com/informalsystems/apalache/issues/2163 *)

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
