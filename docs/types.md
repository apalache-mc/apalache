It is good to have a number of different opinions here. As I can see, we actually have three issues, not one (I initially have put emphasis only on the third issue):

1. How to encode types in TLA+.
1. How to encode type annotations.
1. How to display inferred types.

# How to encode types in TLA+

Everybody has a different opinion here. I agree that it would be cool to use the native TLA+ constructs to express types. My approach may be seen as a hack, but it clearly distinguishes TLA+ from types, which has some merits. The biggest problem I personally have with TLA+ is that it mixes a lot of good and interesting concepts in one logic soup. After I have learned how to separate potatoes from the beans in that soup, I started to appreciate TLA+ :-)

## TypeOK syntax

The only way to write types in the `TypeOK` style is by set membership, e.g.,
`x \in Int`, `f \in [Int -> Int]`, `f \in [SUBSET Int -> SUBSET Int]`, `r \in
[a: Int, b: STRING]`. To declare a that `f` is a set of functions from a tuple
of integers to an integer, we have to write: `f \in SUBSET [Int \X Int ->
Int]`. I personally find that `TypeOK` is quickly making things obfuscated. I
guess, my main problem is that this syntax inevitably requires us to think of
types as sets.
