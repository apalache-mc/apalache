# Project Coordination Guidelines

Arguably, communication is our primary concern throughout the entire process of
designing, implementing, documenting, testing, and disseminating our programs.
But, without question, collaboration on software development calls for a lot of
communication.

This document records our shared (always evolving) understanding of the key ways
we communicate in furtherance of our collaboration. Its intention is to ensure that we are aligned between ourselves in regard to how and why we use the tools we do.

## Elements of our project coordination

We currently use GitHub as the main platform for sharing the communications
that let us coordinate our work. GitHub has a number of different features for
enabling cooperative work, but it's not necessarily obvious what the scope or
intended meaning of each feature is. The following table is used to align our
shared understanding of how to use and interpret the main features:

| Feature                  | Scope                                                   | Communicates...        |
|--------------------------|---------------------------------------------------------|------------------------|
| [issue][issues]          | a distinct problem or task                              | what to work on        |
| [pull request][prs]      | (part of) a solution or fulfillment of a task           | the ongoing work       |
| [milestone][milestones]  | a distinct feature or a closely related set of problems | what work is towards   |
| [label][labels]          | a more or less vague category/topic/quality             | attributes of the work |
| [project board][project] | concurrent human processes with a common dynamic        | how work is done       |
| [discussion][discussion] | free ranging and open discussion                        | whatever               |

(For more on projects vs. milestones, see
https://stackoverflow.com/a/47542346/1187277)

[issues]: https://github.com/informalsystems/apalache/issues
[prs]: https://github.com/informalsystems/apalache/pulls
[milestones]: https://github.com/informalsystems/apalache/milestones
[labels]: https://github.com/informalsystems/apalache/issues/labels
[project]: https://github.com/orgs/informalsystems/projects/30
[discussion]: https://github.com/informalsystems/apalache/discussions

### Project board

Our project board is the main resource to help with our day-to-day coordination. We use a Kanban-styled continuous workflow board with a high level view of whats being done and some queues for what is up next.

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

We are currently considering 3 different prioritization schemes:

1. Action Priority Matrix: This works by us placing our tasks on a matrix
   according to _impact_ and _effort_. Then we analyze the resulting matrix and
   choose what to prioritize, which should be the highest impact and lowest
   effort in general. Here's another explanation
   https://www.mindtools.com/pages/article/newHTE_95.htm
2. Another methodology is [Cost of Delay
   (CoD)](https://kanbanize.com/lean-management/value-waste/cost-of-delay) but
   maybe it is not a good fit for us since it is very tied to economical impact
   of the product. Basically works by asking "What is the (financial) impact of
   this not being completed today?"
3. Finally, perhaps a more subjective strategy would be to have people voting on
   tasks they think are more important and using that as a basis for
   prioritizing.
