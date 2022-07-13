--------------------- MODULE TestAliasNewMissing ------------------------------
\* Syntax for type aliases in Type System 1.2.
\*
\* Here we are missing a type alias, and the type checker should complain.
\*
\* @type: $newAlias => Set($newAlias);
Foo(x) == { x }

===============================================================================
