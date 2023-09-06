<div align="center">
<img
src="https://raw.githubusercontent.com/informalsystems/apalache/99e58d6f5eebcc41f432a126a13a5f8d2ae7afe6/logo-apalache.svg"
alt="Apalache Logo">

<h1><a href="https://apalache.informal.systems/">APALACHE</a></h1>

<p>A symbolic model checker for TLA+<p>

</div>

[![main badge][]][main-ci]

[main badge]: https://github.com/informalsystems/apalache/workflows/build/badge.svg?branch=main
[main-ci]: https://github.com/informalsystems/apalache/actions?query=branch%3Amain+workflow%3Abuild

Apalache translates [TLA+] into the logic supported by SMT solvers such as
[Microsoft Z3]. Apalache can check inductive invariants (for fixed or bounded
parameters) and check safety of bounded executions (bounded model checking). To
see the list of supported TLA+ constructs, check the [supported features]. In
general, Apalache runs under the same assumptions as [TLC].

To learn more about TLA+, visit [Leslie Lamport's page on TLA+] and his [Video
course].

## Releases

Check the [releases page][] for our latest release.

For a stable release, we recommend that you pull the latest docker image with
`docker pull ghcr.io/informalsystems/apalache:main`, use the jar from the
most recent release, or checkout the source code from the most recent release
tag.

To try the latest cool features, check out the head of the [main branch][].

You can also find Apalache packaged via Nix at [cosmos.nix](https://github.com/informalsystems/cosmos.nix)

For more information on installation options, see [the
manual][user-manual-installation].

## Getting started

- Read the [Beginner's tutorial][].
- Check the material at [TLA-Apalache workshop][].
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

## Help wanted

Want to contribute? Here is a list of issues that could be solved without
knowing too much about the internals of Apalache. Solving these issues would
improve usability! Please comment in the relevant issue, if you are going to
solve it.

- Writing annotations in the JSON format: [#804](https://github.com/informalsystems/apalache/issues/804)
- Add support for VIEW in the TLC config: [#851](https://github.com/informalsystems/apalache/issues/851)
- Translate `\E x \in STRING: P` and `\A x \in STRING: P`:
    [#844](https://github.com/informalsystems/apalache/issues/844)
- Interval analysis for `a..b`: [#446](https://github.com/informalsystems/apalache/issues/446)

## Industrial examples

- Check [Light client specs][] and [Model-based testing][] of the Tendermint
  light client.

- Check [Tendermint specs][] to see how we use TLA+ and Apalache at Informal to
  design and specify protocols for the [Tendermint blockchain].

- To see more examples, check the [standard repository of TLA+ examples].

## Talks

- [Informal Systems Tutorial: TLA+ Basics](https://www.youtube.com/watch?v=peKYddIvCIs)

- [Extended version of the Apalache tutorial](https://www.youtube.com/watch?v=Ml7d_3vlH88).
  TLA+ tutorial at DISC 2021 (October 2021).

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
For the details of our novel encoding using SMT arrays, check our
[paper at TACAS23](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_7).
Related reports and publications can be found at the
[Apalache page at TU Wien](http://forsyte.at/research/apalache/).

---

Apalache is developed at [Informal Systems](https://informal.systems/).

With additional funding from<br />[<img alt="the Vienna Business Agency" src="./Wirtschaftsagentur_Wien_logo.jpg" width="200">](https://viennabusinessagency.at/).

Past funding from [Der Wiener Wissenschafts-, Forschungs- und Technologiefonds](https://wwtf.at/about/).

[tla+]: http://lamport.azurewebsites.net/tla/tla.html
[microsoft z3]: https://github.com/Z3Prover/z3
[supported features]: https://apalache.informal.systems/docs/apalache/features.html
[tlc]: http://lamport.azurewebsites.net/tla/tools.html
[leslie lamport's page on tla+]: http://lamport.azurewebsites.net/tla/tla.html
[video course]: http://lamport.azurewebsites.net/video/videos.html
[releases page]: https://github.com/informalsystems/apalache/releases
[master]: https://github.com/informalsystems/apalache/tree/master
[main branch]: https://github.com/informalsystems/apalache/tree/main
[apalache zulip stream]: https://informal-systems.zulipchat.com/#narrow/stream/265309-apalache
[tendermint specs]: https://github.com/tendermint/tendermint/tree/master/spec/light-client/accountability
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
[light client specs]: https://github.com/tendermint/tendermint/tree/master/spec/light-client/verification
[model-based testing]: https://github.com/informalsystems/tendermint-rs/tree/master/light-client/tests/support/model_based#light-client-model-based-testing-guide
[apalache.informal.systems]: https://apalache.informal.systems
[TLA-Apalache workshop]: https://github.com/informalsystems/tla-apalache-workshop
[Beginner's tutorial]: https://apalache.informal.systems/docs/tutorials/entry-tutorial.html
