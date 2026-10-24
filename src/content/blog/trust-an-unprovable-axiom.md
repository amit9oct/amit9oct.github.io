---
title: "Trust: An Unprovable Axiom in Software Verification"
subtitle: Can We Prove Software Is Bug-Free, or Is Trust the Final Axiom?
date: 2026-10-23
tags: [Formal Verification, AI for Code, Specifications, Trusted Computing Base, Proof Assistants]
thumbnail: /assets/img/2026-10-23-Trust/qed-proven-against-reality.webp
---

![A "Q.E.D. – PROVEN*" software correctness insurance policy whose exclusions include specification bugs, compiler bugs, cosmic rays, and Tuesdays](/assets/img/2026-10-23-Trust/qed-insurance-policy.webp)

When I first read [Anthropic's recent work on formal verification](https://www.anthropic.com/research/formal-verification), I was genuinely excited. As a researcher working at the intersection of AI and formal verification, I find it encouraging to see AI pushing the boundaries of what was once prohibitively expensive to verify, and even more encouraging to see the broader community taking notice. The scale of their achievement is remarkable, and the discovery of previously unknown bugs demonstrates the practical value of this direction. Yet, as I watched the enthusiasm spread across X and beyond the formal methods community, I began to worry about something: **are we conflating the ability to prove properties about software with the promise of bug-free software?**

We invest in formal verification much like we invest in insurance—not because things necessarily go wrong, but because we want stronger assurances when the stakes are high. But what exactly are we insuring against, and how much can those assurances really guarantee? These questions brought me back to Ken Thompson's fascinating 1983 Turing Award lecture (published in 1984), *[Reflections on Trusting Trust](https://dl.acm.org/doi/10.1145/358198.358210)*, which I first encountered in a graduate programming languages class. Four decades later, I think his observations about trust are especially relevant in the age of AI. I'll return to both the insurance analogy and Thompson's lecture as we explore what verification can—and cannot—promise.

This is my attempt to **cut through the clutter** surrounding formal verification, particularly now that AI has brought it into the spotlight. Whether you've spent years staring at proof obligations or have never encountered a theorem prover, this essay is for you. I promise to keep the technicalities to a minimum (a dangerous promise coming from someone who works on formal verification). My goal isn't to rain on anyone's parade, least of all Anthropic's. To be fair, Anthropic's write-up does say that "formally verified" does not mean "bug-free." It's in the Limitations section near the end, after the glossy diagrams, which, fittingly, is exactly where an insurance policy keeps the important parts. My concern is less with what they claimed than with how the result is being read. It's to ask what these achievements actually mean, where their guarantees begin and end, and why a little skepticism might be healthy when everyone is celebrating. After all, **if there's one thing verification should teach us, it's to question our assumptions.**

## So, What Exactly Are We Verifying?

Formal verification, in simple terms, is the art of making a mathematical promise about software and then proving that the software keeps it. Instead of testing a program on a million inputs and hoping the million-and-first behaves, we use mathematics to establish that a specified property holds for *all* inputs covered by our assumptions. The catch? **We first have to decide what promise the software is supposed to keep.**

This brings us back to Anthropic. In collaboration with [Theorem](https://theorem.dev/), they set out to tackle one of formal verification's oldest headaches: **scale**. Traditionally, writing mathematical proofs about real-world software has required enormous amounts of expert effort. Their idea was to let Claude do much of that heavy lifting. And the results are remarkable: Claude produced machine-checked proofs for **239 testing entry points across 123 open-source libraries**, at a scale that would have been extraordinarily expensive to achieve manually.

So, what exactly was Claude proving? The researchers started with something software engineers already use: **fuzz tests**. Think of fuzzing as throwing thousands (or millions) of unusual inputs at a program to see if anything breaks. Instead of trying inputs one by one, Anthropic turned these existing tests into mathematical statements asserting that they would never crash or fail their checks for any input within a specified range. Claude then generated proofs about the compiled software itself—not just the source code—and a separate proof checker verified them. In other words, they went from **“we've tried an awful lot of inputs” to “we can prove this test won't fail for any input covered by our model.”** That's a meaningful shift in what testing can guarantee.

The idea of bringing AI, fuzzing, and formal specifications together isn't entirely new, either. A few months earlier, researchers at Bloomberg published [*Agentic Separation Logic Specification Synthesis* (Spec-Agent)](https://arxiv.org/abs/2605.27531), which uses LLMs to generate formal specifications and fuzz testing to check them. The direction is related, although the roles are reversed: Spec-Agent uses fuzzing to validate candidate specifications, while Anthropic uses existing fuzz tests to define properties that Claude can formally prove. **The ingredients aren't entirely new; what Anthropic brings to the table is a particularly ambitious recipe—and a remarkable demonstration of scale.**

But perhaps the most exciting part isn't the sheer number of proofs. **It's that the process uncovered previously unknown bugs and produced patches to fix them.** This is where formal verification goes beyond an academic exercise and demonstrates tangible value for real-world software. Finding bugs that have survived years of testing, and fixing them, is no small achievement. It is precisely the kind of practical impact that makes advances in AI-assisted verification worth celebrating.

### But There's a Catch (Isn't There Always?)

There's a reason fuzzing has been so successful, particularly for low-level software: you can throw all sorts of unexpected inputs at a program and see whether something breaks. Anthropic's approach takes this a significant step further by proving that certain failures cannot occur, rather than merely hoping that enough testing will uncover them.

But **a fuzz test is only as good as the behavior it knows to check**. A program that never crashes can still produce incorrect results, silently corrupt data, or do something spectacularly different from what its users intended. Sometimes a crash is even preferable to a program that confidently tells you everything is fine while quietly doing the wrong thing.

And this gets trickier as we move up the software stack. Fuzzing a parser or a compression library is one thing; specifying the intended behavior of a distributed service, a financial application, or an entire web platform is quite another. Such systems involve state, concurrency, external services, and requirements that evolve with their users. Fuzzing can certainly be applied to these systems too, but translating their full intended behavior into executable checks is considerably harder.

Anthropic's choice of software and execution environment matters here. Their large-scale experiment works with specific fuzzing entry points, bounded inputs of up to 64 MB, and a modeled, single-threaded RISC-V execution environment. These are reasonable engineering choices that make an ambitious verification problem tractable. But they also define the boundaries of the resulting guarantees. Moving from isolated fuzz targets to the correctness of an entire deployed application is not simply a matter of asking Claude to generate a few more proofs.

**Proving that a test never fails doesn't tell us what the test forgot to ask.**

None of this diminishes Anthropic's achievement. In fact, I find the discovery and repair of previously unknown bugs to be the most compelling part of the work. It demonstrates a practical direction for AI and formal methods: not necessarily promising that every piece of software will become bug-free, but building tools that systematically uncover failures and help engineers fix them.

That's a future worth being excited about, even without promising a world in which bugs have gone extinct.

## A Proof Is Only as Good as the Question You Ask

Here's the catch: **a proof assistant is extraordinarily good at answering the question you asked. Unfortunately, it has no obligation to tell you whether you asked the right question.**

In software verification, we call that question a *specification*—a mathematical description of what the software is supposed to do. If the specification says a calculator must never crash, a proof can establish exactly that. The calculator might cheerfully tell you that $2 + 2 = 5$, but as long as it doesn't crash, the proof has kept its promise. Mathematics is remarkably obedient that way.

And therein lies the problem. **We haven't eliminated the need to write correct software; we've moved much of our trust from writing correct code to writing correct specifications.** The specification decides what counts as correct behavior and, equally importantly, what counts as a bug relative to that specification.

A program can satisfy its specification perfectly while doing something nobody actually wanted.

But the challenge isn't merely writing *a* specification. It's writing one that is **meaningful independently of the software we're trying to verify**.

Imagine letting an AI write both the program and its specification. If the program has a bug, what's stopping the AI from writing a sufficiently elaborate chain of `if-else` conditions that faithfully reproduces the bug in the specification? The resulting proof could be perfectly valid. We would have formally established that the program behaves exactly as the program behaves.

Congratulations, we've reinvented the mirror—with a proof certificate!

![A robot holds a buggy divide function up to a mirror; its reflection holds the identical bug under the banner "Implementation ≡ Specification"](/assets/img/2026-10-23-Trust/self-verifying-mirror.webp)

Of course, there's nothing inherently wrong with describing an implementation's existing behavior. That can be valuable for regression testing and checking behavioral equivalence. But it's not the same as independently establishing that the behavior is desirable.

The distinction becomes especially important when AI systems are allowed to generate implementations, specifications, and proofs together. **If the same system gets to decide what correctness means and then demonstrate that it achieved correctness, what exactly have we independently established?**

Anthropic's primary fuzzing experiment avoids the most obvious version of this problem by deriving its high-level obligations from existing fuzz harnesses rather than letting Claude freely invent them. But that still leaves us trusting that the original harnesses captured meaningful properties.

And there's an economic dimension to this that deserves attention.

For decades, one of the arguments against widespread formal verification was that writing proofs required too much expert effort. AI is making impressive progress on precisely that problem. But writing, reviewing, and maintaining meaningful specifications is also an engineering undertaking.

In a world where AI makes proofs increasingly cheap, **the expensive part may no longer be proving that software follows the rules. It may be figuring out what the rules should be.**

We haven't eliminated the possibility of human error; we've simply given it a more mathematical place to hide.

And even if we somehow wrote the perfect specification, would that finally eliminate the need for trust?

## Trusting Trust: It's Turtles All the Way Down

This brings me back to Ken Thompson's *Reflections on Trusting Trust*. In his 1983 Turing Award lecture, Thompson described a wonderfully unsettling trick involving compilers.

A compiler is the program that translates human-readable code into instructions a computer can execute. But there's a rather amusing chicken-and-egg problem: **what compiles the compiler itself?** Compilers are often written in the very languages they compile, so an existing compiler is used to build the next version.

![A staircase of compilers, each built by a simpler one: a modern C compiler, a restricted C compiler, a minimal C compiler, an assembler, machine code, and finally hardware. "Every compiler has a past. How much of it do we trust?"](/assets/img/2026-10-23-Trust/who-compiled-the-compiler.webp)

Thompson demonstrated how a malicious compiler could secretly insert a backdoor into another program while compiling it. The truly clever part? The compiler could also reproduce that malicious behavior whenever it compiled a new version of itself.

You could inspect the source code, remove every trace of the backdoor, and rebuild everything from seemingly clean sources. Yet the malicious behavior would survive, quietly passed from one compiler executable to the next.

**The source code could be innocent while the executable was guilty.**

<p class="aside-link">▶ Watch: <a href="https://www.youtube.com/watch?v=SJ7lOus1FzQ" target="_blank" rel="noopener">Understanding Trusting Trust</a></p>

His warning was simple:

> "No amount of source-level verification or scrutiny will protect you from using untrusted code."

And that raises an uncomfortable question: **if we verify the software, who verifies the tools we used to verify it? And who verifies those tools?**

![The verification stack: source semantics, a verified compiler, and assembly semantics are proved; the assembler, linker, OS, and hardware remain trusted](/assets/img/2026-10-23-Trust/verification-vs-trusted-foundations.webp)

Now, to Anthropic's credit, verifying compiled machine code rather than only source code addresses an important part of this problem. We need not assume that an unverified compiler faithfully translates a source-level proof into the executable under examination.

But the broader question remains. We still need to trust the formal execution model, the proof-checking infrastructure, and ultimately the correspondence between that model and the machine on which the software actually runs.

We can verify compilers, operating systems, and even processor designs. Each step can reduce the assumptions we need to make.

But eventually, our beautiful mathematical proofs must meet physical silicon.

### When Proofs Meet Silicon

Suppose we verify the compiler, the operating system, and even the processor design. Surely, we can finally declare victory?

Unfortunately, **software has an inconvenient habit of existing in the physical world. Mathematics doesn't have that problem.**

A mathematical theorem doesn't suddenly become false because an alpha particle decided to visit. A running program, however, might behave differently because of exactly that.

Alpha particles emitted by trace radioactive materials in chip packaging, and energetic particles associated with cosmic radiation, can disturb electrical charges in semiconductor memory and cause individual bits to flip.

A perfectly verified program might expect a `0` and encounter a `1`, through no fault of its source code, compiler, or proof.

Apparently, even the universe occasionally likes to flip bits.

Of course, we can design hardware to detect and correct such errors. We can even formally verify that a system tolerates certain kinds of faults. But doing so requires us to specify which faults we expect, how they might occur, and what guarantees we want in their presence.

**We haven't eliminated our assumptions; we've simply pushed them another level down.**

At some point, we're trusting that our mathematical model adequately captures the messy physical reality in which our software operates.

This doesn't mean mathematical proofs checked by computers are immune to physical failures either. Rather, the mathematical statement has a meaning independent of the particular machine checking its proof, while claims about deployed software concern actual physical executions.

And this distinction matters. A proof about an execution model can be mathematically impeccable without establishing that every physical execution will conform to that model.

## Suppose We Trust the Hardware. Are We Done Yet?

Let's be generous.

Let's assume that the hardware behaves exactly as expected, no cosmic rays are feeling particularly mischievous, and every instruction executes faithfully. In fact, Anthropic explicitly acknowledges limitations involving its execution model and the difference between verified artifacts and deployed systems.

So, for the sake of argument, let's grant ourselves the perfect machine.

**Surely, now we can declare the software bug-free?**

Not quite.

Software has an inconvenient habit of interacting with other software, users, organizations, and an ever-changing world. And sometimes the most consequential bugs have little to do with whether one isolated program crashes.

Consider the infamous [CrowdStrike outage of July 2024](https://www.crowdstrike.com/en-us/blog/channel-file-291-rca-available/), which brought millions of Windows machines to their knees.

At the technical level, the failure involved an out-of-bounds memory read triggered by a problematic content update. But there's a broader software engineering question: **how did an update capable of bringing down critical systems reach millions of machines in the first place?**

Software engineering has spent decades developing rather unglamorous but essential practices: validating interfaces, reviewing changes, checking compatibility, testing updates, and rolling them out gradually.

These practices matter because software does not exist as an isolated executable. It exists within a system of versions, configurations, dependencies, deployment infrastructure, and human decisions.

Sure, we could formally verify the memory safety of the offending code. We could fuzz-test configurations until the machines beg for mercy.

But what about the larger update protocol?

Under what conditions should a new configuration be accepted? Which software versions must it support? When should a rollout stop? Who decides whether an update is safe enough to deploy?

These aren't necessarily questions a fuzzing harness for a single binary can answer.

To verify them, we'd need to specify the expected behavior of the broader system, including its update and deployment protocols. And that specification might itself become an enormous engineering undertaking, potentially approaching the complexity of the processes we were trying to verify.

**At some point, the hard part isn't proving that the system follows the rules. It's deciding whether we've written down all the right rules.**

None of this means formal methods cannot reason about deployment protocols or distributed systems. They absolutely can. But the relevant properties do not magically materialize because proof construction has become cheaper.

And sometimes the problem is even more subtle: there may not be a crash, a broken protocol, or an obviously incorrect output to point to.

### When Correctness Meets Probability

Consider software that generates cryptographic keys.

Suppose we want those keys to be sampled uniformly at random. We can mathematically specify the desired distribution and formally verify that an algorithm produces it, assuming a suitable source of randomness.

But now imagine observing a handful of generated keys.

Can we prove from those observations alone that the underlying physical source follows the distribution we assumed?

Not really.

Even a perfectly functioning random process can produce extremely unlikely-looking outcomes. And a defective generator can occasionally produce results that look perfectly ordinary.

**Probability has an annoying habit of refusing to provide certainty on demand.**

The problem isn't that probability cannot be modeled mathematically. Quite the opposite: probability theory gives us powerful tools for reasoning about randomized systems.

The problem is the relationship between the mathematical model and the real-world process that the model is supposed to describe.

A formal proof might tell us precisely how an algorithm behaves *if* its source of randomness has certain properties. It doesn't automatically establish that the physical source actually has those properties.

Once again, we have reached a boundary where something must be trusted, measured, or independently justified.

And the broader lesson is that **even a perfectly formalized requirement can depend on assumptions that its proof does not establish.**

## Software Is a Living Organism. Mathematics, Not So Much.

There's another reason I find the recent successes of AI in mathematics fascinating when viewed alongside AI-assisted software verification.

Consider the [Navier–Stokes Millennium Prize Problem](https://www.claymath.org/millennium/Navier-Stokes-Equation/), which asks profound mathematical questions about the behavior of solutions to the equations governing fluid motion.

Whether AI eventually helps resolve questions like these is fascinating in its own right. But there's something fundamentally different about the nature of the problem.

**The theorem doesn't change because someone released Navier–Stokes 2.0 on Tuesday.**

A mathematical theorem concerns specific mathematical objects under precisely stated assumptions. Mathematicians may refine definitions, discover new formulations, or change the questions they investigate. But once a particular statement is fixed, its truth isn't subject to customer feedback, a product manager's roadmap, or a production incident.

Software, however, is a living organism.

It grows, evolves, acquires dependencies, interacts with new environments, and occasionally develops behaviors nobody remembers asking for. What counted as correct behavior yesterday might be considered a bug tomorrow.

![Mathematics carved in stone beside software as a living, growing tree](/assets/img/2026-10-23-Trust/stone-math-living-software.webp)

And sometimes, what everyone thought was a bug becomes a feature.

Software engineers have built entire careers around this distinction.

This creates an important difference between proving mathematical theorems and proving that software behaves as people intend.

In mathematics, the statement being proved is often itself the object of interest. In software, the specification is our attempt to describe something outside mathematics: **what humans actually want a system to do.**

And human intentions, unlike mathematical definitions, are rarely written in stone.

That doesn't mean every mathematical conjecture is easy to specify or every software requirement is vague. But software correctness introduces another kind of challenge: the specification must remain connected to a changing system and the people who use it.

We can prove that software satisfies a specification. We can even prove that it continues satisfying that specification after certain changes.

But whether the specification still captures what people need is a question mathematics alone cannot settle.

**A proof can tell us that we've built what we specified. It cannot, by itself, tell us that we specified what we wanted.**

## Trust, but Verify. Then What?

Remember the insurance analogy from the beginning? We buy insurance for our bad days, not because we expect something to go wrong, but because we'd rather not face the consequences unprepared. Yet buying insurance doesn't make us immortal (if only the paperwork were that powerful!). We still need to read the fine print, understand what the policy covers, and, perhaps most importantly, **trust that the insurance company will actually pay when things go wrong.** A policy can be perfectly valid and still fail to cover the one disaster you needed it for. Turns out, skipping the terms and conditions isn't a great idea when your house is on fire.

Formal verification isn't so different in this respect. **The specification is our insurance policy: it defines what is covered, under which conditions, and what falls outside the guarantee.** The proof establishes that the software satisfies those conditions, but the assurance is only as meaningful as the specification itself. And just as we trust the insurance company to honor its promises, we must trust the assumptions, tools, and physical systems that connect mathematical proofs to running software. Neither insurance nor verification eliminates risk; both require us to understand precisely what we've been promised.

![A formal verification policy: coverage of stated properties under stated assumptions, valid only if the specification is correct; exclusions for wrong specifications, compiler assumptions, hardware faults, and reality behaving unexpectedly](/assets/img/2026-10-23-Trust/formal-verification-policy.webp)

And perhaps that's perfectly fine. **Formal verification doesn't need to promise bug-free software to be extraordinarily useful.** Anthropic's work demonstrates this beautifully: the ability to uncover previously unknown bugs, help repair them, and establish rigorous guarantees at an unprecedented scale is already a substantial achievement. We should celebrate that without asking verification to perform miracles it never promised.

But personally, I'm even more excited about turning the question around. Much of the recent enthusiasm has focused on **using AI to make formal verification better**. What about the inverse: **using formal verification to make AI better?**

Instead of treating a proof as the final certificate attached to an AI-generated program, imagine verification becoming part of how AI systems learn, reason, and generate in the first place. Formal feedback could help models recognize their mistakes, improve their reasoning, discover vulnerabilities, and develop a better understanding of whether their outputs satisfy independently meaningful specifications. Rather than simply asking AI to produce more proofs, we could use proofs to help AI produce better software.

![A loop of human intent, specifications, counterexamples, corrections, and verified feedback turning an error-prone AI into a more reliable one](/assets/img/2026-10-23-Trust/verification-helping-ai.webp)

Of course, this doesn't magically solve the specification problem either. We would still need to decide what properties matter, how to represent human intentions, and which guarantees deserve our trust. In fact, bringing verification closer to AI makes those questions even more important. A model trained to satisfy a poorly chosen specification might become exceptionally good at doing precisely the wrong thing. **We've already taught AI to optimize objectives. Perhaps we should spend a little more time worrying about who wrote the objectives.**

I don't believe the future of formal methods lies in verifying everything indiscriminately. I believe it lies in making verification accessible, economical, and deeply integrated into the places where it provides meaningful assurance. Sometimes that means proving a critical safety property. Sometimes it means finding a vulnerability nobody knew existed. And sometimes it means using formal feedback to make an AI system more reliable before its output ever reaches production.

There's another question that has been occupying my own research lately: **as AI gets better at producing formal representations of what we ask for, how do we know those representations actually mean what we intended?** It's a question I find at least as fascinating as whether AI can prove them. I suspect the next exciting advances won't just be about making proofs cheaper, but about making the guarantees behind them more meaningful.

I hope to have more to share on that front soon. For now, let's just say that **proving the right thing might be a more interesting problem than proving things right.**

Ken Thompson's warning remains relevant four decades later. We can push the boundaries of what we prove, shrink our trusted computing bases, and make remarkable progress toward trustworthy software. But somewhere, whether in our specifications, our tools, our hardware, or our understanding of human intent, trust remains.

**Trust is not a failure of verification. Pretending that verification has eliminated the need for trust is.**