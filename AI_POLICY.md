# Apalache AI Usage Policy

The Apalache project has strict rules for AI usage:

- **All AI usage in any form must be disclosed.** You must state the tool you
used (e.g. Codex, Claude Code, Cursor, Copilot) along with the extent that the
work was AI-assisted.

- **The human-in-the-loop must fully understand all code.** If you can't explain
what your changes do and how they interact with the greater system without the
aid of AI tools, do not contribute to this project.

  In particular, if you are new to Scala, you must be able to explain all
  programming constructs in your contribution. AI tools are great helpers for
  learning. Use them to understand your code. The project maintainers do not have
  to remember all of Scala by heart. Hence, we tend to use the common
  subset of the language and idioms that are understood by humans.

- **Issues and discussions must be written by humans.** AI tools are good at
producing lengthy prose, but this prose is hard to read for humans. We prefer
text that demonstrates human reasoning. It is okay to have spelling and grammar
mistakes, as long as you have put some thinking into your writing.

  If you use AI to do research, you may quote the results of that research in a
  clearly marked blockquote. However, you must verify the results before quoting
  them, and you must trim the results down to the relevant information.

- **Descriptions of Pull Requests must be written by humans.** Pull requests
should specify: the intent of the change, the key design decisions, the system
parts affected, and the key changes (briefly). The size of the PR text must be
proportional to the size of the change. A 10-line change does not need a 5-page
description.

- **No AI-generated media is allowed (art, images, videos, audio, etc.).** Text
and code are the only acceptable AI-generated content, per the other rules in
this policy.

- **The number of active Pull Requests is limited.** It takes effort to open a
high-quality Pull Request. You have to prioritize your contributions and submit
the important ones first.

- **Signed-off-by and Developer Certificate of Origin.** AI agents MUST NOT add
Signed-off-by tags. Only humans can legally certify the Developer Certificate of
Origin (DCO). The human submitter is responsible for:

  - Reviewing all AI-generated code

  - Ensuring compliance with licensing requirements

  - Adding their own Signed-off-by tag to certify the DCO

  - Taking full responsibility for the contribution

  Moreover, read the [LF Guidance on Generative AI][lf-generative-ai] to
  understand the copyright and licensing implications of using AI tools.

**The above rules apply only to outside contributions to Apalache**. Maintainers
are exempt from these rules and may use AI tools at their discretion. They have
proven themselves trustworthy to apply good judgment.

## There are Humans Here

Please remember that Apalache is maintained by humans. About 99% of the code has
been written by humans. This means that many design and coding decisions do not
follow the canned recipes of the AI tools. Due to that, the AI tools may fail to
understand the intent behind the code.

Every discussion, issue, and pull request is read and reviewed by humans (and
sometimes machines, too). It is a boundary point at which people interact with
each other and the work done. It is rude and disrespectful to approach this
boundary with low-effort, unqualified work, since it puts the burden of
validation on the maintainers. Most of the time, the maintainers are not paid
for doing this work, and they aim at improving the project quality, not reading
the inference of AI tools.

## AI is Welcome Here

The active maintainers of Apalache are using the AI tools themselves. We embrace
the use of AI. We are careful about the Apalache design and code, as almost all
of the code has been written by humans, who put plenty of their thought into it.

**Our reason for the strict AI policy is not due to an anti-AI stance**. We
understand that many external contributors are trying to help the project. We
also know that it is tempting to shoot an AI tool at a problem and see it
"solved". Unfortunately, the AI tools do not have understanding of the impact of
their code. We often see the code that may even solve the issue, but it is not
properly integrated into the system, nor is it properly tested. As a result,
the maintainers have to spend hours of their time on fixing code that was
generated in 10 minutes.

## References

This policy derives from the following AI policies and guidelines:

 - Large parts of the [Ghostty AI Policy][ghostty-ai-policy]
 - [Linux Foundation Generative AI Policy][lf-generative-ai]
 - [Kernel Coding Assistants][kernel-coding-assistants]

[ghostty-ai-policy]: https://github.com/ghostty-org/ghostty/blob/main/AI_POLICY.md
[lf-generative-ai]: https://www.linuxfoundation.org/legal/generative-ai
[kernel-coding-assistants]: https://kernel.org/doc/html/next/process/coding-assistants.html