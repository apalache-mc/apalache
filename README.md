<div align="center">
<img
src="https://raw.githubusercontent.com/informalsystems/apalache/99e58d6f5eebcc41f432a126a13a5f8d2ae7afe6/logo-apalache.svg"
alt="Apalache Logo">

<h1><a href="https://apalache.informal.systems/">APALACHE</a></h1>

<p>A symbolic model checker for TLA+<p>

</div>

[![unstable badge][]][unstable-ci]

[unstable badge]: https://github.com/informalsystems/apalache/workflows/build/badge.svg?branch=unstable
[unstable-ci]: https://github.com/informalsystems/apalache/actions?query=branch%3Aunstable+workflow%3Abuild

Apalache translates [TLA+] into the logic supported by SMT solvers such as
[Microsoft Z3]. Apalache can check inductive invariants (for fixed or bounded
parameters) and check safety of bounded executions (bounded model checking). To
see the list of supported TLA+ constructs, check the [supported features]. In
general, Apalache runs under the same assumptions as [TLC].

To learn more about TLA+, visit [Leslie Lamport's page on TLA+] and his [Video
course].

## Releases

Check the [releases page][].

For a stable release, we recommend that you run the latest docker image
`apalache/mc:latest` or checkout the source code from our latest release tag.

To try the latest cool features, check out the [unstable branch][].

For more information on installation options, see [the
manual][user-manual-installation].

## Getting started

- Read the [Apalache user manual][user-manual].
- Consult the (WIP) [Idioms for writing better TLA+][idioms].
- Consult the (WIP) [TLA+ language manual for engineers][language-manual].

## Website

Our current website is served at https://apalache.informal.systems .

The site is hosted by github, and changes can be made through PRs into the
[gh-pages](https://github.com/informalsystems/apalache/tree/gh-pages) branch of
this repository. See the README.md on that branch for more information.

The user documentation is automatically deployed to the website branch as per
the [CI configuration](./.github/workflows/deploy.yml).

Our old website is still available at https://forsyte.at/research/apalache/ .

## Community

- Join the chat in the [Apalache zulip stream].
- [Contribute](./CONTRIBUTING.md) to the development of Apalache.

## Industrial examples

- Check [Light client specs] and [Model-based testing] of the Tendermint
  light client.

- Check [Tendermint specs] to see how we use TLA+ and Apalache at Informal to
  design and specify protocols for the [Tendermint blockchain].

- To see more examples, check the [standard repository of TLA+ examples].

## Talks

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

## Performance

We are collecting [apalache benchmarks]. See the Apalache performance when
[checking inductive invariants] and running [bounded model checking]. Versions
0.6.0 and 0.7.2 are a major improvement over version 0.5.2 (the version
[reported at OOPSLA19](https://dl.acm.org/doi/10.1145/3360549)).

## Academic papers

To read an academic paper about the theory behind Apalache,
check our [paper at OOPSLA19](https://dl.acm.org/doi/10.1145/3360549).
Related reports and publications can be found at the
[Apalache page at TU Wien](http://forsyte.at/research/apalache/).

---

Apalache is developed at [Informal Systems](https://informal.systems/).

With additional funding from [<img alt="the Vienna Business Agency" src="./Wirtschaftsagentur_Wien_logo.jpg" width="200">](https://viennabusinessagency.at/).

[tla+]: http://lamport.azurewebsites.net/tla/tla.html
[microsoft z3]: https://github.com/Z3Prover/z3
[supported features]: ./docs/features.md
[tlc]: http://lamport.azurewebsites.net/tla/tools.html
[leslie lamport's page on tla+]: http://lamport.azurewebsites.net/tla/tla.html
[video course]: http://lamport.azurewebsites.net/video/videos.html
[releases page]: https://github.com/informalsystems/apalache/releases
[master]: https://github.com/informalsystems/apalache/tree/master
[unstable branch]: https://github.com/informalsystems/apalache/tree/unstable
[apalache user manual]: ./docs/manual.md
[idioms for writing better tla+]: ./docs/idiomatic
[apalache zulip stream]: https://informal-systems.zulipchat.com/#narrow/stream/265309-apalache
[tendermint specs]: https://github.com/tendermint/spec/tree/master/rust-spec
[tendermint blockchain]: https://github.com/tendermint
[standard repository of tla+ examples]: https://github.com/tlaplus/Examples
[apalache benchmarks]: https://github.com/informalsystems/apalache-tests
[checking inductive invariants]: https://github.com/informalsystems/apalache-tests/blob/master/results/001indinv-report.md
[bounded model checking]: https://github.com/informalsystems/apalache-tests/blob/master/results/002bmc-report.md
[user-manual]: http://informalsystems.github.io/apalache/docs/index.html
[user-manual-docker]: https://apalache.informal.systems/docs/apalache/installation/docker.html
[user-manual-installation]: https://apalache.informal.systems/docs/apalache/installation/index.html
[language-manual]: https://apalache.informal.systems/docs/lang/index.html
[idioms]: https://apalache.informal.systems//docs/idiomatic/index.html
[light client specs]: https://github.com/tendermint/spec/tree/master/rust-spec/lightclient/verification
[model-based testing]: https://github.com/informalsystems/tendermint-rs/tree/master/light-client/tests/support/model_based#light-client-model-based-testing-guide
[apalache.informal.systems]: https://apalache.informal.systems
