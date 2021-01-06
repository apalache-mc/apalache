<!-- NOTE: We use some kramdown to tweak the styling here. -->

<!-- For refdef, see see https://stackoverflow.com/a/31712482/1187277 -->
{:refdef: style="text-align: center;"}
!["Apalache Logo"](./logo-apalache.png "Apalache Logo"){: height="100px"}
{:refdef}

[Features][] • [User manual][] • [Releases][] • [User chat][] • [Contribute][]
{: style="font-size: 1.2em; text-align: center;"}

Apalache translates [TLA+][] into the logic supported by SMT solvers such as
[Microsoft Z3][]. Apalache can check [inductive invariants][] (for fixed or
bounded parameters) and check safety of bounded executions ([bounded model
checking][]). To see the list of supported TLA+ constructs, check the supported
features. In general, Apalache runs under the same assumptions as [TLC][].

To learn more about TLA+, visit [Leslie Lamport's page on TLA+][] and see his
[video course][].

## Talks and tutorials

- [How TLA+ and Apalache Helped Us to Design the Tendermint Light Client](https://www.crowdcast.io/e/interchain-conversations-II/38).
    Interchain Conversations 2020 (December 2020).

- [Model-based testing with TLA+ and Apalache](https://youtu.be/aveoIMphzW8).
  TLA+ Community Event 2020 (October 2020).

- [Type inference for TLA+ in Apalache](https://youtu.be/hnp25hmCMN8).
  TLA+ Community Event 2020 (October 2020).

- [Formal Spec and Model Checking of the Tendermint Blockchain Synchronization Protocol](https://youtu.be/h2Ovc1KWlXM)
  2nd Workshop on Formal Methods for Blockchains (July 2020).

- [Showing safety of Tendermint Consensus with TLA+ and Apalache](https://www.youtube.com/watch?v=aF20-28sMII).
  Dev session at Informal Systems (May 2020).

- [TLA+ model checking made symbolic](https://www.youtube.com/watch?v=e66FGgRzaqw)
  OOPSLA 2019 (October 2019).

- [Bounded model checking of TLA+ specifications with SMT](https://www.youtube.com/watch?v=Xl1--arESl8)
  TLA+ Community Event 2018 (July 2018).

## Academic papers

To read an academic paper about the theory behind Apalache,
check our [paper at OOPSLA19](https://dl.acm.org/doi/10.1145/3360549).
Related reports and publications can be found at the
[Apalache page at TU Wien](http://forsyte.at/research/apalache/).


<!-- LINKS -->

[TLA+]: http://lamport.azurewebsites.net/tla/tla.html
[Microsoft Z3]: https://github.com/Z3Prover/z3
[Features]: ./docs/features.md
[TLC]: http://lamport.azurewebsites.net/tla/tools.html
[Leslie Lamport's page on TLA+]: http://lamport.azurewebsites.net/tla/tla.html
[Video course]: http://lamport.azurewebsites.net/video/videos.html
[Releases]: https://github.com/informalsystems/apalache/releases
[Contribute]: https://github.com/informalsystems/apalache/blob/unstable/CONTRIBUTING.md
[User manual]: ./docs/manual.md
[User chat]: https://informal-systems.zulipchat.com/#narrow/stream/265309-apalache
[inductive invariants]: https://github.com/informalsystems/apalache-tests/blob/master/results/001indinv-report.md
[bounded model checking]: https://github.com/informalsystems/apalache-tests/blob/master/results/002bmc-report.md
