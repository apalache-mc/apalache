# Project Coordination Guidelines

Arguably, communication is our primary concern throughout the entire process of
designing, implementing, documenting, testing, and disseminating our programs.
But, without question, collaboration on software development calls for a lot of
communication.

This document records our shared (always evolving) understanding of the key ways
we communicate in furtherance of our collaboration. Its intention is to ensure that we are aligned between ourselves in regard to how and why we use the tools we do.

**NOTE**: This document is primarily for internal use among the core development
team and it may include links to resources that are not accessible publicly.

## Elements of our project coordination

We currently use GitHub as the main platform for sharing the communications that
let us coordinate our work. GitHub has a number of different features for
enabling cooperative work, but it's not necessarily obvious what the scope or
intended meaning of each feature is. We also use several communication protocols
channels that are synchronized via git, but unrelated to GitHub's features.

The following table is used to align our
shared understanding of how to use and interpret the main features:

| Element                      | Scope                                                   | Communicates...                         |
|------------------------------|---------------------------------------------------------|-----------------------------------------|
| [label][labels]              | a more or less vague category/topic/quality             | attributes of the work                  |
| [issue][issues]              | a distinct problem or task                              | what to work on                         |
| [pull request][prs]          | (part of) a solution or fulfillment of a task           | the ongoing work                        |
| [milestone][milestones]      | a distinct feature or a closely related set of problems | what related work items amount to       |
| [ADRs and RFCs][adr and rfc] | a decision or design that will have broad impact        | deliberation and reasons for a decision |
| [project board][project]     | concurrent human processes with a common dynamic        | how work is coordinated within Apalache |
| [OKR workflow explorer][okr] | dependencies to other efforts within Informal Systems   | how work is coordinated within Informal |
| [strategy map][strategy]     | arch of major work on a one to two year horizon         | where different work streams converge   |
| [discussion][discussion]     | free ranging and open discussion                        | whatever                                |

(For more on projects vs. milestones, see
https://stackoverflow.com/a/47542346/1187277)

[adr and rfc]: https://github.com/apalache-mc/apalache/tree/main/docs/src/adr
[discussion]: https://github.com/apalache-mc/apalache/discussions
[issues]: https://github.com/apalache-mc/apalache/issues
[labels]: https://github.com/apalache-mc/apalache/issues/labels
[milestones]: https://github.com/apalache-mc/apalache/milestones
[okr]: https://informal-workflow-explorer.netlify.app/
[project]: https://github.com/orgs/apalache-mc/projects/30
[prs]: https://github.com/apalache-mc/apalache/pulls
[strategy]: https://github.com/apalache-mc/strategy/blob/main/projects/apalache/yearly2021-2022/plan2022.md

Some of these elements call for special discussion.

### Project board

Projects coordinate perpetual, ongoing **processes** used by **people**.

> A Project answers the question, "What are we working on at the moment?"
> ([source](https://stackoverflow.com/a/47542346/1187277))

Our project board is the main resource to help with ongoing our day-to-day
coordination. We use a Kanban-styled continuous workflow board with a high level
view of whats being done and some queues for what is up next.

#### Why

The column order in the board represents different points in the timeline:

| Input  | WIP     | Output |
|--------|---------|--------|
| Future | Present | Past   |

Our focus should be on the present, and we should look at the future and the
past to support the present.

For the **present**, we can use the board to help with:
- Visual feedback of what is being done
- Capacity management
- Tactical coordination

For the **future**:
- Prioritization
- Aligning expectations
- Value assessment

For the **past**:
- Metrics
- Celebrations
- Knowledge dissemination

#### How

##### Using the **Next** column

Generally, a backlog is something we cannot control. If a new bug is identified,
it has to go into some sort of backlog and there is nothing we can do about it.
Having something so dynamic as our only queue of work is a problem because of
the overhead it would take to maintain it.

A "Next" column is a subset of our backlog that we can fully control, and the
idea is for it to hold the tasks that we will work on once we finish what is in
progress. Therefore, there should be some sort of prioritization criteria to
help us define which tasks from the backlog should go in this queue. The process
of deciding which tasks should be on the "Next" column is usually called
"replenishment".

The Next column needs a size limit since "if everything is a priority, then
nothing is a priority".

###### How do we prioritize work?

We use a modified action-priority matrix. Our prioritization process is
recorded in
[RFC-021](https://github.com/apalache-mc/apalache/blob/main/docs/src/adr/021rfc-prioritization.md)

### Milestones

[Milestones](https://en.wikipedia.org/wiki/Milestone) mark discrete points in
our **progress**. Milestones can be **finished**, at which point they are closed.
This records that the target point has been reached.

> An [open] milestone answers the question, "What is remaining to finish this product?"
> ([source](https://stackoverflow.com/a/47542346/1187277))

Milestones collect a set work items that build towards a distinct feature or
articulate a complex problem. We use them focus future towards specific,
achievable, goals, and to record the history of the work done towards these
ends.

#### Why

Much of work involves complex sets of tasks that all work towards a single end.
E.g., designing and implementing a novel feature or testing hypotheses that
requires many related experiments or complicated set ups. It is important to be
able to keep this broader goals in view, even while we break them up into
smaller sub tasks to allow us to focus on more manageable units of work.

It is also useful and encouraging to see how much planned work remains before
such goals are reached.

#### How

[According to
GitHub](https://docs.github.com/en/issues/using-labels-and-milestones-to-track-work/about-milestones)

> You can use milestones to track progress on groups of issues or pull requests in a repository.

Progress tracking is supported by the following features:

- A description of the goal to be completed.
- An optional due date.
- A completion percentage meter, showing how much work remains to be done.
- A list of all the open and closed work items grouped under the milestone.

Note that an issue or PR can only belong to a single milestone.

### Labels

Labels are for categorizing issues into groups based on certain shared qualities
of the planned work, or based on some common attribute. Labels are very flexible
and freeform. They can server as catchall buckets for groupings that don't fit
into the time-based buckets of project boards or the product-based buckets of
milestones.

#### Why

Labels let us add metadata to work items, which we can then use for filtering
and grouping the work. These filters can provide a flexible mechanisms for
giving different kinds of insights into planned or completed work. Filters on
labels can be combined, allowing us to mix perspectives: I.e., we might see just
those issues which are good for first time contributors **and** that fix bugs.

#### How

A good label serves to help a user or contributor see our project from a
distinct, useful perspective.  Multiple labels can be assigned to the same work
items, since an item may exhibit many overlapping qualities, and they can be
seen from many different points of view.

Some examples of useful labels are:

- Label issues that are good for first time contributors.
- Label issues that report bugs vs. issues that request features.
- Label issues that propose refactoring or maintenance work, so you can track
  how much time we are devoting to paying down our technical debt.
- Label issues that are "chores" so you can prevent overloading anyone with
  unpleasant work.

There are only two constraints limiting the content of a label:

1. Don't use labels to indicate the status of ongoing work. That is represented
   by the *status* defined in whatever projects the work item belongs to.
2. Don't use a label for trying to group issues that build towards a common goal
   (e.g., issues that implement a new feature). That is represented by a
   [milestone](#milestones).

An additional consideration is that having too many labels can reduce their
effectiveness: the more lables in use, the more difficult it becomes to select
the right labels for an issue, and the more likely we are to see multiple labels
introduced for the same purpose.
