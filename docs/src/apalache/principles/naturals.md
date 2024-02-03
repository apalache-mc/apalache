
### Naturals

If you look carefully at the [HOWTO on annotations](../../HOWTOs/howto-write-type-annotations.md), you will find that
there is no designated type for naturals. Indeed, one can just use the type
`Int`, whenever a natural number is required. If we introduced a special type
for naturals, that would cause a lot of confusion for the type checker. What
would be the type of the literal `42`? That depends on, whether you extend
`Naturals` or `Integers`. And if you extend `Naturals` and later somebody else
extends your module and also `Integers`, should be the type of `42` be an
integer?

Apalache still allows you to extend `Naturals`. However, it will treat all
number-like literals as integers. This is consistent with the view that the
naturals are a subset of the integers, and the integers are a subset of the
reals.  Classically, one would not define subtraction for naturals. However,
the module `Naturals` defines binary minus, which can easily drive a variable
outside of `Nat`. For instance, see the following example:

```tla
{{#include ../../../../test/tla/NatCounter.tla::}}
```

Given that you will need the value `Int` for a type annotation, it probably
does not make a lot of sense to extend `Naturals` in your own specifications,
as you will have to extend `Integers` for the type annotation too.

