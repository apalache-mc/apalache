---
authors: Shon Feder, Gabriela Moreira
last revised: 2022-05-24
---

# ADR-20: Prioritization of Work

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

In the context of the distributed development of Apalache\
facing repeated friction around unplanned work and lack of agreement on priorities\
we decided to adopt an Action Priority Matrix\
to achieve shared understanding and agreement on prioritization\
accepting the additional overhead required by scoring and evaluating our work items.\

## Context

In recent months, we have repeatedly encountered conflicts over prioritization
of our work. Different members within our team, or different stakeholders
outside of the team, have voiced opposing views on what work items deserve
focused and urgent attention. In reflecting on these occasions in our meetings,
we have come to agree that these conflicts are due, at least in part, to lack of
a clearly established framework for assessing, communicating, and recording the
priority of work.

In particular, when plans change, or when urgent, unplanned work needs
attention, we would like a lightweight framework for reaching consensus on the
new priorities, and deriving a new ordering of the work to be done.

The decision to adopt an action priority matrix for prioritizing our work was
reached in [December of 2021][dec-decision], but we weren't clear at that time
how to we would determine the scores for each work item. This ADR aims to
outline and codify the approach we will use.

## Options

We considered 3 different approaches to prioritization: 

1. [Action Priority Matrixj][apm]: We score each work item based on the expected
   _effort_ it will require to complete and the anticipated _impact_ of the
   results.  We then  place these tasks on a matrix and coordinate the scores to
   optimize for the highest value delivery with the least effort.
2. [Cost of Delay (CoD)][cod]: Similar to the action priority matrix, this is
   based on assigning two scores to work items: _value_ and _urgency_. These
   scores are then correlated to minimize the negatives financial impacts of
   delays. It basically works by asking "What is the (financial) impact of this
   not being completed today?" 
3. Voting: Finally, we discussed a more subjective strategy based on having
   people vote on tasks they think are more important and using that as a basis
   for prioritizing.

### References

More information on various approaches to prioritization can be found in these
sources we consulted:

- http://www.tarrani.net/linda/prioritizing.pdf
- https://www.mindtools.com/pages/article/newHTE_95.htm
- https://www.productplan.com/glossary/action-priority-matrix/
- https://cio-wiki.org/wiki/Action_Priority_Matrix_(APM)
- https://kanbanize.com/lean-management/value-waste/cost-of-delay

## Solution

### Decision

We felt that the CoD approach was too dependent on the need to determine
short-term financial returns. This is hard to square with our role as an open
source, R&D center serving Informal Systems and the aims of correct software
development in the community at large.

We felt that the unstructured voting approach was too subjective. Moreover,
while it would work to surface our individual preferences, it doesn't help
establish a common ground for shared understanding about priorities.

We finally decided to adopt the _Action Priority Matrix_. We feel that the
process is light-weight enough that we can implement it without slowing down our
development but rigorous enough to root our shared understanding in the
objective needs and constraints we face in our work.

### Process

We follow an adapted version of [the approach to APM described in the CIO Wiki][apm].

#### Categories

APM leads us to divide work items into four categories, as follows:

| _Impact_ **\\** _Effort_ | **Low Effort** | **High Effort**   |
|--------------------------|----------------|-------------------|
| **High Impact**          | "Quick Wins"   | "Major Projects"  |
| **Low Impact**           | "Fill-ins"     | "Thankless tasks" |

The category within which a work item falls determines the general approach
taken towards the work:

| Category        | Approach                                           |
|-----------------|----------------------------------------------------|
| Quick wins      | Do ASAP                                            |
| Major projects  | Sustain long term focus                            |
| Fill-ins        | Do in spare time, but never taking time from above |
| Thankless tasks | Avoid, unless there's literally nothing else to do |

#### Scoring

We determine which category a work item falls under based on the _impact_ and
_effort_ scores assigned to the work. We therefore need a shared understanding
of how to assess the impact and effort of a work item. We register only 3 levels
on each axis to keep the cognitive load of reckoning scores minimal.

Scores are recorded by affixing labels to the github issue tracking the work item.

##### Effort

Effort is scored best on a rough estimate of the amount of focused time it would
take to complete a work item:

- Easy **`e0`**: Can be completed within about 1 day
- Medium **`e1`**: Can be completed within 3 days
- Difficult **`e2`**: Will take 5 or more days

Ideally, as soon as we recognized that an actively planned ticket will take more
than 5 days of focused work, we would factor it into smaller tickets, allowing
us to avoid perpetually prolonged monster tickets. But some people may prefer to
track "major projects" with a single issue rather than a milestone, and this
doesn't pose a significant problem.

##### Impact

Impact is scored based on considering impact in the follow 4 domains:

1. _User / customer_: The benefit of the results of a work item to our users and
   customers
2. _Mission_: Furtherance of our organization's mission and objectives
3. _Invention_: Advancement of state of the art in formal verification and
   specification
4. _Development_: Improvements to our development capacities and bandwidth
   (which supports advancing the other three factors).

- High **`i0`**:
  - User / customer: Unblocks critical work
  - Mission: Advances critical organizational objectives
  - Invention: Opens up novel verification and specifications abilities
  - Development: Saves > 3 hours per week
- Medium **`i1`**:
  - User / customer: Unblocks non-critical work
  - Mission: Advances non-critical organizational objectives
  - Invention: Makes incremental improvement to verification and specification
    abilities
  - Development: Saves between 1 to 3 hours per week
- Low **`i2`**:
  - User / customer: Improves functionality, but an easy workaround exists
  - Mission: No significant advance of organizational objectives
  - Invention: No significant improvement to verification and specification abilities
  - Development: Saves < 1 hours per week

### Prioritization and evaluation

The initial priority of a requirement should be established at the time work is
agreed upon, including when setting plans quarterly and when triaging unplanned
work. All collaborators with a stake in the work are responsible for ensuring
the work is scored in a way that they feel to be correct.

When unplanned work is introduced, the stakeholders involved should determine
its score (using informal language, when needed), and this should be used to
decided whether it is worth interrupting any ongoing or planned work.

When deciding which work item to take on next, we should favor work that is
nearest to scoring minimum effort and maximum impact: (`e0`, `i0`). Ties should
be resolved based on the worker's inclination or discussions within other
stakeholders.

The priority of work should be re-evaluated as the situation changes. E.g.:

- When goals change, then impact should be reconsidered.
- If we discover work was incorrectly scoped, then the effort should be
  reevaluted.

We can generate views into the 4 quadrants via filters in our project board, or
any other tooling or visualization we find suitable. When reviewing work
in progress or queued up next at our weekly meetings, we should always be
sure that the highest priority work on the board is being addressed.

## Consequences

TBD
<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->

[cod]: https://kanbanize.com/lean-management/value-waste/cost-of-delay
[apm]: https://cio-wiki.org/wiki/Action_Priority_Matrix_(APM)
[Karl Weiger]: https://en.wikipedia.org/wiki/Karl_Wiegers
[first-things-first]: http://www.tarrani.net/linda/prioritizing.pdf
[dec-decision]: https://github.com/informalsystems/apalache/commit/f379a717ca02a559b8f48d503f4413410d0b8abd
