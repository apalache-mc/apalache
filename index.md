<!-- NOTE: We use some kramdown to tweak the styling here. -->

<!-- For refdef, see see https://stackoverflow.com/a/31712482/1187277 -->
{:refdef: style="text-align: center;"}
!["Apalache Logo"](./logo-apalache.png "Apalache Logo"){: height="100px"}
{:refdef}

[Installation][] • [Manual][] • [Releases][] • [Chat][] • [Contribute][]
{: style="font-size: 1.2em; text-align: center;"}

Apalache translates [TLA+][] into the logic supported by SMT solvers such as
[Microsoft Z3][]. Currently, Apalache supports three approaches of analyzing
TLA<sup>+</sup> specifications:

 1. Randomized symbolic execution to reason about **some** executions up to
 length `k`,
 
 1. Bounded model checking to reason about **all** executions up to length `k`,
 and
 
 1. Inductiveness checking to reason about **all** executions of **all**
 lengths.

To understand, how these three approaches play together, see the
[[blogpost]][Ben-Or] on Model checking safety of Ben-Or's Byzantine consensus
with Apalache (2024).

In general, Apalache runs under the same assumptions as the explicit-state model
checker [TLC][]. To learn more about TLA<sup>+</sup>, visit [Leslie Lamport's
page on TLA+][] and see his [video course][]. Also, check out [TLA+ language
manual for engineers](https://apalache-mc.org/docs/lang/index.html).

In addition to TLA<sup>+</sup>, Apalache power ups the following projects:
 
 - The [Quint language][] provides an engineer-friendly syntax for writing
   specifications. Quint uses Apalache as a backend model checker.

 - [Solarkraft][] is a tool for runtime monitoring of Soroban smart contracts on
 Stellar. Solarkraft uses Apalache as a backend model checker.
 
 - [Atomkraft][] is a tool for model-based testing of Cosmos dApps.
   Atomkraft uses Apalache as a backend model checker.

## Success stories

- Specification and Model-checking of the ZKsync Governance Protocol
[[blogpost]][zksync] (2024)

- Specification and model checking of BFT consensus by Matter Labs
[[blogpost][chonkybft]] (2024)

- Model checking of the Tendermint light client [[results page]][light-client]
(2020)

- Model checking of agreement and accountable safety in Tendermint consensus
[[results page]][tendermint] (2019-2020)

## Tutorials

- [Extended version of the Apalache tutorial](https://www.youtube.com/watch?v=Ml7d_3vlH88)

- [Type checking TLA+ with Snowcat](https://apalache-mc.org/docs/tutorials/snowcat-tutorial.html)

## Theory

To read an academic papers about the theory behind Apalache, check our [paper at
OOPSLA19][oopsla19] and [paper at TACAS23][tacas23].

## Talks

- [How TLA+ and Apalache Helped Us to Design the Tendermint Light Client](https://www.crowdcast.io/e/interchain-conversations-II/38).
    Interchain Conversations 2020 (December 2020).

- [Informal Systems Tutorial: TLA+ Basics](https://www.youtube.com/watch?v=peKYddIvCIs)

- [Model-based testing with TLA+ and Apalache](https://youtu.be/aveoIMphzW8).
  TLA+ Community Event 2020 (October 2020).

- [Formal Spec and Model Checking of the Tendermint Blockchain Synchronization Protocol](https://youtu.be/h2Ovc1KWlXM)
  2nd Workshop on Formal Methods for Blockchains (July 2020).

- [Showing safety of Tendermint Consensus with TLA+ and Apalache](https://www.youtube.com/watch?v=aF20-28sMII).
  Dev session at Informal Systems (May 2020).

- [Type inference for TLA+ in Apalache](https://youtu.be/hnp25hmCMN8).
  TLA+ Community Event 2020 (October 2020).

- [TLA+ model checking made symbolic](https://www.youtube.com/watch?v=e66FGgRzaqw)
  OOPSLA 2019 (October 2019).

- [Bounded model checking of TLA+ specifications with SMT](https://www.youtube.com/watch?v=Xl1--arESl8)
  TLA+ Community Event 2018 (July 2018).


<!-- LINKS -->

[Chat]: https://apalache.discourse.group/
[Contribute]: https://github.com/apalache-mc/apalache/blob/main/CONTRIBUTING.md
[Features]: ./docs/apalache/features.html
[Installation]: ./docs/apalache/installation/index.html
[Leslie Lamport's page on TLA+]: http://lamport.azurewebsites.net/tla/tla.html
[Manual]: ./docs
[Microsoft Z3]: https://github.com/Z3Prover/z3
[Releases]: https://github.com/apalache-mc/apalache/releases
[TLA+]: http://lamport.azurewebsites.net/tla/tla.html
[TLC]: http://lamport.azurewebsites.net/tla/tools.html
[Video course]: http://lamport.azurewebsites.net/video/videos.html
[Quint language]: https://quint-lang.org/
[Ben-Or]: https://protocols-made-fun.com/specification/modelchecking/tlaplus/apalache/2024/11/03/ben-or.html
[zksync]: https://protocols-made-fun.com/zksync/matterlabs/quint/specification/modelchecking/2024/09/12/zksync-governance.html
[chonkybft]: https://protocols-made-fun.com/consensus/matterlabs/quint/specification/modelchecking/2024/07/29/chonkybft.html
[tendermint]: https://github.com/cometbft/cometbft/blob/main/spec/light-client/accountability/Synopsis.md
[light-client]: https://github.com/cometbft/cometbft/blob/main/spec/light-client/README.md
[tacas23]: https://link.springer.com/chapter/10.1007/978-3-031-30823-9_7
[oopsla19]: https://dl.acm.org/doi/10.1145/3360549
[Solarkraft]: https://github.com/freespek/solarkraft/
[Atomkraft]: https://github.com/informalsystems/atomkraft