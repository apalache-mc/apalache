This is a copy of the specification that was downloaded from:

https://github.com/tlaplus/Examples/blob/master/specifications/Bakery-Boulangerie/Bakery.tla

The Boulangerie Algorithm in PlusCal/TLA<sup>+</sup>
====================================================

The boulangerie algorithm is a variant of the bakery algorithm published in

_Under the Hood of the Bakery Algorithm: Mutual Exclusion as a Matter of Priority  
by Yoram Moses and Katia Patkin  
22nd International Colloquium on Structural Information and Communication Complexity (SIROCCO 2015)._

I had already written a PlusCal version of the bakery algorithm for the [TLA<sup>+</sup> Hyperbook](http://lamport.azurewebsites.net/tla/hyperbook.html), along with a formal proof that it satisfies mutual exclusion. The proof was checked with TLAPS, the TLA<sup>+</sup> proof system. Just for fun, I decided to modify the algorithm and the proof for the boulangerie algorithm. Here are the two algorithms and their proofs:

[Bakery.tla](Bakery.tla)  
    The source file of the bakery algorithm specification and its pretty-printed pdf version.

[Boulanger.tla](Boulanger.tla)  
    The source file of the boulangerie algorithm specification and its pretty-printed pdf version. Comments at the beginning of the file describe the process of writing the algorithm and constructing the proof.
