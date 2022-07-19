------------------------- MODULE TestAliasNew ---------------------------------
\* Syntax for type aliases in Type System 1.2.
\*
\* @typeAlias: newAlias = UNINTERPRETED_TYPE;
\* @type: $newAlias => Set($newAlias);
Foo(x) == { x }

===============================================================================
