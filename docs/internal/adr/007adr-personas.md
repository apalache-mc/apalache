# ADR-007: Collection of personas

In this document, we collect personas, that is, descriptions of people who
could use TLA+ at their work one day. More importantly, we emphasize the goals
that they pursue. We follow the technique that is described in [Alan Cooper's
Book][]. Most likely, the Apalache team will target a small subset of these
personas (optimally, 2-3). We have to understand, who of them need us most.

Personas are not real people, they usually share features of several people we
have met. We probably run in stereotypes and exaggerations in these
descriptions. No offence meant! To invent personas' names, we look at the last
names of movie actors.  We also add academic titles to person names, as
Apalache builds upon academic research, so we feel that it is important to
distinguish the academic background from industrial background. If you feel
that one of these descriptions and their name match to well to you, please let
us know. We can always change the name of a persona.

# Dr. Alina Apatow, specification engineer

Alina has a PhD in computer science and training in mathematical logic.  Hence,
she is not afraid of formal methods. She can write software in Golang, Rust,
and Python. However, she is not doing that on daily basis.  Alina believes that
specification and verification help engineers in writing better software.

Alina's job is to turn informal protocol design documents into precise formal
specifications.  She is proud of figuring out how those sloppy documents in
English fit together and uncovering the actual protocol ideas behind the wall
of English words. She has a great ability of translating illogical things
into logic. When Alina finds an inconsistency in a informal description of a
protocol, she knows that she is doing great job. When Alina finds a bug in a
formal specification, she gets an appraisal from her peers, who never thought
that such an issue was possible.

As Alina does not have plenty of time to contemplate about protocols, she
prefers using tools for navigating through specifications and trying protocols
in various configurations and under various scenarios.

Alina's goals are:

 1. Maintain dozens of protocol specifications, both in English and TLA+.

 1. Quickly update specifications as her peers and customers come up with new
 ideas.

 1. Make sure that the specifications do not have obvious flaws.

 1. Make sure that the specifications satisfy safety, liveness, and security
 properties that were envisioned by protocol designers, for some test
 configurations.

# Dr. Joseph Jacobs, protocol designer

Joseph has a PhD in computer science. He has published several papers on
distributed algorithms at ACM PODC and DISC. Joseph can run distributed
algorithms in his head, he does not need a feeble computer to do that. He is
very proud of this ability, and he ecstatic when he predicts bugs by this
analysis alone. He also knows how to fix those bugs. If only engineers asked
him earlier!

Joseph's job is to understand distributed protocols and design new ones.  He
has an industry job, so Joseph has to talk to engineers. He pays a lot of
attention to turn sloppy thinking into precise mathematical writing. Joseph is
quite happy about his mathematical proofs. When somebody is telling him that
new cool technology is there, he feels skeptical. What can be better than
pencil and paper? However, he wants to try new technology, if it can do boring
work for him.

Joseph's goals are:

 1. Write protocol specifications in prose and mathematics, PODC-style.

 1. Write mathematical proofs of correctness of his protocols.

 1. Avoid writing code and avoid jumping into implementation details.

 1. Communicate his protocol knowledge to engineers.

 1. Review new protocols that come from the engineers.

 1. Explain new hypes to business people.

# Charles Carbone, blockchain engineer

Charles is working at a blockchain startup. He has recently graduated from
college, but he has already learned a lot about software engineering. Charles
knows how to code for Ethereum, Cosmos, Polkadot, and dozen of other
blockchains.  He knows Rust, Golang, Wasm, and Solidity. Charles is enthusiastic
about all trends that happen in the blockchain world.  Recently, he has heard
about this verification thing that can help engineers to find bugs in smart
contracts.

Charles's job is to develop new features for the new cool blockchain technology
that is called Ceratops. Charles is writing unit tests for his features, but he
understands that it is hard to test his code in the blockchain under all
possible scenarios. From time to time, he runs his code in a simulator and
finds bugs.

Charles's goals are:

 1. Develop the best blockchain technology, which is of course Ceratops.

 1. Push new features faster than other blockchain companies do.

 1. Understand new protocols and APIs that other engineers push into Ceratops.

 1. Integrate cool technology in Ceratops.

 1. Learn new languages and libraries.

 1. Hang out with other cool blockchain kids.

# Henry Hacker, blockchain security expert

Henry is running his own company called Alwalkeria. He is a CEO of Alwalkeria.
In fact, he is also CFO, CTO, and the sales department, as he is the only
person working in his company. Henry has been coding since he turned five (is
it even possible?). He can code in Rust, Go, C++, Java, Python, JavaScript, and
probably a dozen of other programming languages. Although he tried all these
languages, he never had patience to write a piece of software longer than 5
KLOC. He knows the architecture of all hardware by Intel and Apple, and he
likes to dig into binaries down to the assembly level. 

Henry's job is to find bugs in the code that is written by other people.  He is
well paid for that. As the blockchain space is now offering money for hacker
challenges, he is participating in those challenges. While Henry has found bugs
in plenty of Solidity contracts, he was honest to report on these bugs to the
developers, instead of just stealing the coins. Henry is using a number of
tools to figure out the bugs, some of these tools are quick hacky scripts
of his own production.

Henry's goals are:

 1. Find bugs in code that is written by others.

 1. Get rewarded for finding the bugs.

 1. Find more bugs to get rewarded more. More shallow bugs is ok,
 deep bugs require more time.

 1. Climb mountains and travel around the world.

# Bill Banks, senior systems engineer

Bill is a senior engineer at a software company. He has been developing
software for 10 years, and he is leading a team of 7 engineers. His team is
following the Agile methodology to develop their new distributed system
Oviraptor. They are developing Oviraptor in short sprints, use continuous
integration and deploy their system often. Bill is promoting maximum
automation. He is now excited about property-based testing.

Bill is sceptical about investments in testing. As a result, his team is busy
adding features and has no time for testing beyond writing simple unit tests
(and PBT). Bill believes that time to market is short and if the code does not
crash in a few standard cases, it should be deployed. If the system crashes,
the customer's admins will restart it. More jobs for the admins!

Bill's goals are:

 1. Add more features in the system as fast as possible.

 1. Iterate!

 1. Get more users by having more features than their competitors.

 1. Avoid time-consuming testing, better offload it to somebody else.

TODO: we probably do not understand Bill's goals. 

# Max Mueller, enterprise systems architect

Max has been working in software engineering for 15 years. He knows Java (or
.NET) inside out. He has been designing back-end systems that integrate with
relational databases, message queues, enterprise buses, etc. Max is a systems
architect at a software company that is developing an enterprise solution.
When somebody is sending him a link about a new shiny tool that was posted at
Hackernews, Max is sneering: He has seen too many silver bullets in his life.

Max has to deal with a large system that consists of multiple layers of
software and interacts with several other enterprise systems. Max documents his
decisions and interacts with engineers. He has been drawing diagrams (UML,
Visio) and writing text specifications, but he is not happy about state of the
art.

Max's goals are:

 1. Design a complex system with many interacting components.

 1. Document his solutions and communicate them to engineers.

 1. Find conceptual flaws in the design.

 1. Find performance bottlenecks in the architecture.

 1. Communicate enterprise protocols to other architects.

# Stephen Sanderson, software engineer and FP enthusiast

Stephan recently graduated from one of the top universities, with major in
computer science. He is working at a startup and reads about all cool
technology that appeared today on Hacker news. Sometimes, he even reads papers
from ACM POPL, but not the old ones, that's too uncool, only the latest ones.
He knows Haskell, Scala, OCaml, Rust, and other cool languages, even though he
might code in something more mainstream like Python or JavaScript at work.

Stephen read about Coq, Isabelle, Agda, Idris and tried some of these tools.
He is a big fan of Curry-Howard correspondence. He knows 50 recipes of coffee
and wonders why most the people don't know the difference between Espresso and
Macchiato. It is not surprising that Stephen likes to use strongly typed languages.
He believes that dependent types are the future of programming languages.

Stephen's goals are:

 1. Write aesthetically-pleasing code.

 1. Try cool technology.

 1. Systematize all of his work in types and categories.

TODO: add more goals? A few goals probably means that we do not understand Stephen. 

# S. Sankar, undergraduate student

Sankar is studying at one of the top US universities. He is the best student in
his class.  He is attending a class on distributed systems, where the professor
gave Sankar an optional exercise to specify a challenging algorithm in TLA+.

Sankar's goals are:

 1. Learn TLA+ as fast as possible and with minimal effort.

 1. Specify the algorithm in TLA+.

 1. Get the best score for his exercise.

# Dr. Valeria Velasquez, verification engineer

Valeria has a PhD in computer science. She wrote her thesis on verification
techniques for the new gamma-theta-rho calculus. She has verified a simplified
version of the famous Technosaurus protocol. This is an awesome scientific
result, provided that the reader is able to read the Technosaurus protocol in
the gamma-theta-rho calculus. Well, several reviewers of Valeria's papers
managed to understand it!

Valeria is working in a new aggressive startup that offers verification
services and security audits to other companies. Valeria's job is to provide
the customers with a formal certificate of that customer's systems work correctly.
She is using Coq, Dafny, Ivy, CBMC, and Verifast to verify some parts of the
customers' protocols and code. It takes Valeria lots of efforts to express
customers' artifacts in the verification languages that are accepted by all
these tools. Even worse, all these languages are so different from one another
that it is not clear how the verification results match.

Valeria's goals are:

 1. Convince the customers that they need verification.

 1. Express customer's artifacts in languages that are accepted by verification
 tools.

 1. Deliver verification results in a reasonable time frame of several weeks.

 1. Explain the customer what has been proven about their systems.

 1. Explain the customer what could not be proven and why.

 1. Communicate with customer's engineers to refine her understanding of the
 customer's systems and refine her specs.

 1. Explain to the customer's engineers the bugs that she found during
 verification.

# Prof. Zoe Zambovski, PL researcher

Prof. Zambovski has been publishing papers at ACM POPL and occasionally at CAV
for over 20 years. She has been serving on program committees of top
conferences for a long time. Recently, Prof. Zambovski has acquired the
prestigious ERC Advanced Grant, in which she promises to develop new languages
and analysis techniques for distributed systems. Her new project is called
"MassivePulsar".

Prof. Zambovski has recently hired two postdocs and five PhD students to work
on MassivePulsar.

Prof. Zambovski's goals are:

 1. Find research topics for her team in the framework of MassivePulsar.

 1. Submit research papers at top venues in PL and get them accepted,
 so her research must be cutting edge and received well by the reviewers.

 1. Get her PhD students defend in time and find jobs related to MassivePulsar.

 1. Teach classes to undergraduate students by using something less cutting
 edge than MassivePulsar.

[Alan Cooper's Book]: https://www.goodreads.com/book/show/44098.The_Inmates_Are_Running_the_Asylum
