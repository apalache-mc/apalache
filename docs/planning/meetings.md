# Apalache meeting log

**Sticky note (do not move):** Let's keep it simple. The meeting agenda and
notes go in this file. The updates to this file are made via GitHub pull
requests. By doing so, we make sure that:

 - All team members have a chance to see the updates, via the GitHub interface,
 - All team members may add their points to the agenda and meeting notes,
 - We use the tools that we master (our text editors and GitHub),
 - We do not have to transfer the common knowledge between email, notion, roam,
   google docs, or whatever comes next.
   


## Meeting agenda 10.12.2020

*Please add your ideas!*

Igor:

  - What we do well:
   - tactical planning: github issues, bugfixes
   - peer-reviewing
   - the infrastructure has improved a lot thanks to @shonfeder
   - research prototypes

  - What we do not do well (shame on me):
   - no well-defined strategic planning (hey, it was a research project!)
   - our milestones are more like features:
     - the deadlines in the milestones are never met (because our milestones
       are not milestones)
     - due to the nature of our project, many features need 1-2 months of work
     - there are a lot of interdependencies between different features,
       so our milestones are creeping
     - see the [new features](./features.png)
   - new features are hard to merge, sometimes, breaking the builds
   - need for more systematic and automatic testing of new features: they should come
     with unit tests and integration tests
   - We do "move fast and break things", but we never know when the tool is
     stable enough to cut a relase
   - Hard to cut a release, as `unstable` accumulates the code of the partially
     implemented features

  - As we are doing more engineering now, we have to define and codify our
    engineering process:

   - we need to formulate (and document) a common understanding of:
     - how we organize large chunks of development
        (merely introducing a milestone does not help)
     - how we test new features
     - how we check test coverage of the new features
     - how we test bugfixes and collect regression tests
     - how we merge new features without stepping on one another's toes
     - how we integrate all above in the github infrastructure

   - our project has a heavy research component:
     - the techniques are documented in the research papers
     - as a result, it is hard to understand several modules by just reading the code
     - new techniques are first implemented as research prototypes and are
       made stable with time

   - we should pick the best practices from the processes that suit our
     project.  The planning-oriented processes seem to be very heavy on
     form-filling, e.g.,
     [TSP](https://en.wikipedia.org/wiki/Team_software_process) and the
     [introduction in
     TSP](https://www.oreilly.com/library/view/introduction-to-the/9780321579294/).
     Agile processes seem to be to fragile for developing a compiler-like tool.
     We should pick the best practices from both. For instance, I am developing
     new code with
     [TDD](https://en.wikipedia.org/wiki/Test-driven_development).
   
   - we should extract useful HOWTOs from the known processes: planning, structuring
     development cycles (features, milestones), doing meetings, measuring
     enchancements (e.g., in unit and integration tests).

   - we should avoid
     heavy bureaucracy, e.g., we should not waste our time on filling time
     sheets (though it is a good idea to personally track your time).

   - we should avoid writing a survey on all available development processes.



