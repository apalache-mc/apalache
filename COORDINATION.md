# Project Coordination Guidelines

Arguably, communication is our primary concern throughout the entire process of
designing, implementing, documenting, testing, and disseminating our programs.
But, without question, collaboration on software development calls for a lot of
communication.

This document records our shared (always evolving) understanding of the key ways
we communicate in furtherance of our collaboration.

## Elements of our project coordination

We currently use GitHub as the main platform for sharing the communications
that let us coordinate our work. GitHub has a number of different features for
enabling cooperative work, but it's not necessarily obvious what the scope or
intended meaning of each feature is. The following table is used to align our
shared understanding of how to use and interpret the main features:

| Feature      | Scope                                                   | Communicates...        |
|--------------|---------------------------------------------------------|------------------------|
| issue        | a distinct problem or task                              | what to work on        |
| pull request | (part of) a solution or fulfillment of a task           | the ongoing work       |
| milestone    | a distinct feature or a closely related set of problems | what work is towards   |
| label        | a more or less vague category/topic/quality             | attributes of the work |
| project      | concurrent human processes with a common dynamic        | how work is done       |
| discussion   | free ranging and open discussion                        | whatever               |

(For more on projects vs. milestones, see
https://stackoverflow.com/a/47542346/1187277)

### Open Questions:

- Should onboarding new members be a "milestone"?
    - On the one hand, it's a closely related set of work.
    - On the other hand, members might not like to have that vsibible, and it's not a milestone on a particular product (perhaps using a private repo for this?)
    - On the one hand again, why shouldn't we treat this kind of work grouping like any other? If we are using issues to track our work but not putting onboarding stuff into the issues, it ends up as untracked work.
- How can we visualize past, current and future milestones?
    - We currently don't create milestones for things we have not started
    - GitHub doesn't provide a board visualization of milestones
    - It's probably better to think about prioritization in terms of milestones
 
## How do we prioritize work?


Gabriela:

> About the methodology I mentioned: it's called Action Priority Matrix, and works by us placing our tasks on a matrix according to impact and effort. Then we can analyze the resulting matrix and choose what to prioritize, which should be the highest impact and lowest effort in general. Here's another explanation 
>
> https://www.mindtools.com/pages/article/newHTE_95.htm

Another methodology is [Cost of Delay (CoD)](https://kanbanize.com/lean-management/value-waste/cost-of-delay) but maybe it is not a good fit for us since it is very tied to economical impact of the product. Basically works by asking "What is the (financial) impact of this not being completed today?"

A perhaps more subjective strategy would be to have people voting on tasks they think are more important and using that as a basis for prioritizing.


### Using the Next column

Generally, a backlog is something we cannot control. If a new bug is identified, it has to go into some sort of backlog and there is nothing we can do about it. Having something so dynamic as our only queue of work is a problem because of the overhead it would take to maintain it.

A "Next" column is a subset of our backlog that we can fully control, and the idea is for it to hold the tasks that we will work on once we finish what is in progress. Therefore, there should be some sort of priorization criteria to help us define which tasks from the backlog should go in this queue. The process of deciding which tasks should be on the "Next" column is usually called replenishment.

The next column needs a size limit since "if everything is a priority, then nothing is a priority"

## Overall workflow reflection

The columns order in a board represent different points in the timeline

| Input | WIP | Output |
|---|---|---|
| Future | Present | Past |

Our focus should be on the present, and we should look at the future and the past to support the present.

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
