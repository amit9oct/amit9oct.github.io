---
title: "Trust: An Unprovable Axiom in Software Verification"
subtitle: Can We Prove Software Is Bug-Free, or Is Trust the Final Axiom?
date: 2026-10-23
tags: [Formal Verification, AI for Code, Specifications, Trusted Computing Base, Proof Assistants]
thumbnail: /assets/img/2026-10-23-Trust/qed-proven-against-reality.webp
---

![A "Q.E.D. – PROVEN*" software correctness insurance policy whose exclusions include specification bugs, compiler bugs, cosmic rays, and Tuesdays](/assets/img/2026-10-23-Trust/qed-insurance-policy.webp)

When I first read [Anthropic's recent work on formal verification](https://www.anthropic.com/research/formal-verification), I was genuinely excited. As a researcher at the intersection of AI and formal verification, seeing proofs scale to real-world software—and uncover previously unknown bugs—was thrilling. But as enthusiasm spread across X and beyond the formal methods community, I began to wonder: **are we conflating proving properties about software with the promise of bug-free software?**

We invest in verification much like insurance: for stronger assurances when the stakes are high. But what exactly are we covered against? That question brought me back to Ken Thompson's 1983 Turing Award lecture (published in 1984), *[Reflections on Trusting Trust](https://dl.acm.org/doi/10.1145/358198.358210)*, which I first encountered in a graduate programming languages class. Four decades later, its questions about trust feel remarkably current. I'll return to both.

This is my attempt to **cut through the clutter**, for readers with or without a formal methods background. I'll keep the technicalities light (a dangerous promise from someone who works on verification). I'm not here to rain on Anthropic's parade: they explicitly acknowledge that "formally verified" doesn't mean "bug-free." It's in the Limitations section, after the glossy diagrams—which, fittingly, is where insurance policies keep the important parts. My concern is how the result is being read. **If verification teaches us anything, it's to question our assumptions.**

## So, What Exactly Are We Verifying?

Formal verification, in simple terms, is the art of making a mathematical promise about software and then proving that the software keeps it. Instead of testing a program on a million inputs and hoping the million-and-first behaves, we use mathematics to establish that a specified property holds for *all* inputs covered by our assumptions. The catch? **We first have to decide what promise the software is supposed to keep.**

This brings us back to Anthropic and [Theorem](https://theorem.dev/), tackling formal verification's perennial headache: **scale**. Proofs of real-world software traditionally demand enormous expert effort. Claude did much of the heavy lifting, producing machine-checked proofs for **239 testing entry points across 123 open-source libraries**—an impressive scale.

What was Claude proving? The team began with **fuzz tests**: programs that throw unusual inputs at software and check whether something breaks. Anthropic turned existing fuzz harnesses into mathematical obligations that the tests never crash or fail their checks within a specified input range. Claude proved properties of the *compiled binaries*, checked by a separate proof checker. They moved from **“we tried an awful lot of inputs” to “this test cannot fail for any input covered by our model.”** That's a meaningful leap.

The ingredients aren't entirely new. Earlier this year, researchers at Bloomberg published [*Agentic Separation Logic Specification Synthesis* (Spec-Agent)](https://arxiv.org/abs/2605.27531), using LLMs to propose specifications and fuzzing to test them. Anthropic uses existing fuzz tests to define properties Claude then *proves*. Different recipes, overlapping ingredients—and Anthropic's remarkable contribution is the scale of the proof-making.

More exciting than the proof count? **The process discovered previously unknown bugs and produced patches.** Finding and fixing bugs that survived years of testing demonstrates the practical value of AI-assisted verification better than any mountain of proof certificates.

### But There's a Catch (Isn't There Always?)

Fuzzing works especially well on low-level software, and Anthropic takes it further: rather than waiting for tests to reveal failures, they prove the modeled failures cannot occur.

But **a fuzz test is only as good as the behavior it knows to check**. A program that never crashes can still produce incorrect results, silently corrupt data, or do something spectacularly different from what its users intended. Sometimes a crash is even preferable to a program that confidently tells you everything is fine while quietly doing the wrong thing.

This gets trickier higher up the software stack. Fuzzing a parser is one thing; capturing the intended behavior of a distributed service or financial application—with concurrency, external dependencies, and evolving requirements—is another. Those systems can be fuzzed, too, but meaningful checks are much harder to write.

The chosen targets matter. Anthropic verifies particular fuzz entry points with inputs up to 64 MB under a modeled, single-threaded RISC-V environment. Sensible constraints—but also boundaries. Moving from those targets to an entire deployed application isn't just a matter of asking Claude for a few more proofs.

**Proving that a test never fails doesn't tell us what the test forgot to ask.**

That's why I find the bug discovery and repair more compelling than claims of universal correctness: these tools can uncover failures and help engineers fix them, without promising to make bugs extinct.

## A Proof Is Only as Good as the Question You Ask

Here's the catch: **a proof assistant is extraordinarily good at answering the question you asked. Unfortunately, it has no obligation to tell you whether you asked the right question.**

In software verification, we call that question a *specification*—a mathematical description of what the software is supposed to do. If the specification says a calculator must never crash, a proof can establish exactly that. The calculator might cheerfully tell you that $2 + 2 = 5$, but as long as it doesn't crash, the proof has kept its promise. Mathematics is remarkably obedient that way.

**Much of our trust has moved from writing correct code to writing correct specifications.** The specification defines correctness—and which behaviors count as bugs relative to it.

The challenge is writing a specification **meaningful independently of the software we're trying to verify**.

Imagine an AI writing both code and specification. If the code has a bug, it could write enough `if-else` branches to reproduce that bug in the specification. The proof could be perfectly valid: the program behaves exactly as the program behaves.

Congratulations, we've reinvented the mirror—with a proof certificate!

![A robot holds a buggy divide function up to a mirror; its reflection holds the identical bug under the banner "Implementation ≡ Specification"](/assets/img/2026-10-23-Trust/self-verifying-mirror.webp)

Describing existing behavior is useful for regression tests and behavioral equivalence. It just isn't independent evidence that the behavior is desirable.

**If the same AI defines correctness and then proves it achieved correctness, what have we independently established?**

Anthropic avoids the most obvious version of this trap by deriving obligations from existing fuzz harnesses. But we still trust those harnesses to express something meaningful.

Proof-writing has long been expensive. AI is changing that, but specifying, reviewing, and maintaining the *right* properties remains substantial engineering work.

As proofs get cheaper, **the expensive part may be deciding what the rules should be.**

We haven't eliminated the possibility of human error; we've simply given it a more mathematical place to hide.

And even if we somehow wrote the perfect specification, would that finally eliminate the need for trust?

## Trusting Trust: It's Turtles All the Way Down

In *Reflections on Trusting Trust*, Ken Thompson described a wonderfully unsettling compiler trick.

A compiler turns human-readable code into executable instructions. But **what compiles the compiler itself?** Compilers can be written in the languages they compile, using an existing compiler to build the next generation.

![A staircase of compilers, each built by a simpler one: a modern C compiler, a restricted C compiler, a minimal C compiler, an assembler, machine code, and finally hardware. "Every compiler has a past. How much of it do we trust?"](/assets/img/2026-10-23-Trust/who-compiled-the-compiler.webp)

Thompson showed how a malicious compiler could insert a backdoor into another program—and quietly reproduce its own malicious behavior when compiling a new compiler.

Even rebuilding from clean source could preserve the backdoor, passed silently between compiler binaries.

**The source code could be innocent while the executable was guilty.**

<p class="aside-link">▶ Watch: <a href="https://www.youtube.com/watch?v=SJ7lOus1FzQ" target="_blank" rel="noopener">Understanding Trusting Trust</a></p>

His warning was simple:

> "No amount of source-level verification or scrutiny will protect you from using untrusted code."

And that raises an uncomfortable question: **if we verify the software, who verifies the tools we used to verify it? And who verifies those tools?**

![The verification stack: source semantics, a verified compiler, and assembly semantics are proved; the assembler, linker, OS, and hardware remain trusted](/assets/img/2026-10-23-Trust/verification-vs-trusted-foundations.webp)

To Anthropic's credit, verifying compiled machine code addresses part of this problem: the guarantee needn't depend on trusting a compiler to preserve a source-level proof.

But we still rely on the execution model, proof-checking infrastructure, and the connection between formal instructions and physical machines.

We can verify more of the stack and shrink those assumptions.

But eventually, our beautiful mathematical proofs must meet physical silicon.

### When Proofs Meet Silicon

Suppose we've verified even the processor design. Victory?

Unfortunately, **software has an inconvenient habit of existing in the physical world. Mathematics doesn't have that problem.**

A theorem doesn't become false because an alpha particle pays a visit. A running program can behave differently for exactly that reason.

Alpha particles from trace contaminants in chip packaging, or energetic particles from cosmic radiation, can disturb memory cells and flip bits.

A verified program can expect `0` and encounter `1`, through no fault of its proof.

Apparently, even the universe occasionally likes to flip bits.

We can detect, correct, and even formally model such faults. But then we must specify which faults to expect and trust that our model is adequate.

**We haven't eliminated our assumptions; we've simply pushed them another level down.**

Machine-checked mathematical proofs aren't immune to faulty computers either. But a theorem's meaning is independent of its checker, while the correctness of deployed software depends on physical execution.

## Suppose We Trust the Hardware. Are We Done Yet?

Let's assume perfect hardware, obedient cosmic rays, and faithful execution. Anthropic itself acknowledges the gap between modeled artifacts and deployed systems.

**Surely, now we can declare the software bug-free?**

Not quite.

Software also interacts with other software, organizations, users, and an ever-changing world. Not every consequential failure is a crashing binary.

Consider the infamous [CrowdStrike outage of July 2024](https://www.crowdstrike.com/en-us/blog/channel-file-291-rca-available/), which brought millions of Windows machines to their knees.

A faulty content update triggered an out-of-bounds memory read. But **how did an update capable of crashing critical systems reach millions of machines?**

Software engineering already has decidedly unglamorous safeguards: compatibility checks, reviews, validation, staged rollouts.

Software lives amid versions, configurations, deployment infrastructure, and human decisions.

Sure, we could formally verify the memory safety of the offending code. We could fuzz-test configurations until the machines beg for mercy.

But what about the larger update protocol?

Which configurations are safe? Which versions are compatible? When should a rollout stop?

Verifying the entire update protocol requires specifying that broader process—potentially an enormous engineering undertaking itself.

**At some point, the hard part isn't proving that the system follows the rules. It's deciding whether we've written down all the right rules.**

Formal methods can reason about such protocols. But their meaningful requirements won't materialize just because proofs get cheaper.

### When Correctness Meets Probability

Consider cryptographic key generation. We can prove an algorithm samples uniformly *assuming* its source of randomness has the right properties.

Can a handful of generated keys prove the physical source obeys that distribution?

No.

A sound generator can produce suspicious-looking results; a defective one can produce ordinary-looking ones.

**Probability has an annoying habit of refusing to provide certainty on demand.**

Probability *can* be modeled and verified mathematically.

But proving an algorithm correct *given* a random source doesn't establish that the real source satisfies those assumptions.

**Even a precise formal guarantee can rest on assumptions its proof doesn't establish.**

## Software Is a Living Organism. Mathematics, Not So Much.

Consider the [Navier–Stokes Millennium Prize Problem](https://www.claymath.org/millennium/Navier-Stokes-Equation/), which asks deep questions about the equations governing fluid motion.

**The theorem doesn't change because someone released Navier–Stokes 2.0 on Tuesday.**

Mathematicians can revise formulations and ask new questions. But once a statement is fixed, its truth doesn't depend on customer feedback or next quarter's roadmap.

Software, however, is a living organism.

It grows dependencies, gains features, meets new environments, and develops behaviors nobody remembers requesting. Yesterday's correct behavior may be tomorrow's bug.

![Mathematics carved in stone beside software as a living, growing tree](/assets/img/2026-10-23-Trust/stone-math-living-software.webp)

And sometimes, what everyone thought was a bug becomes a feature.

Software engineers have built entire careers around this distinction.

In mathematics, the statement being proved is often itself the object of interest. In software, the specification is our attempt to describe something outside mathematics: **what humans actually want a system to do.**

And human intentions, unlike mathematical definitions, are rarely written in stone.

Not every theorem is easy to formalize or every software requirement vague. But software specifications must stay connected to changing systems and users.

We can verify compliance with a specification, even across certain changes.

Whether it still describes what people want is another question.

**A proof can tell us that we've built what we specified. It cannot, by itself, tell us that we specified what we wanted.**

## Trust, but Verify. Then What?

Remember the insurance analogy? We buy insurance for our bad days. It doesn't make us immortal (if only the paperwork were that powerful!). We must read the fine print and **trust that the insurance company will pay when things go wrong.** A perfectly valid policy might exclude precisely the disaster we needed it for. Turns out, reading terms and conditions *after* your house catches fire isn't ideal.

Formal verification has a similar fine-print problem. **The specification is our policy: it defines coverage, conditions, and exclusions.** The proof establishes compliance, but we still trust the specification, tools, and physical system connecting mathematics to execution. Insurance and verification work differently, of course; neither makes reading the conditions optional.

![A formal verification policy: coverage of stated properties under stated assumptions, valid only if the specification is correct; exclusions for wrong specifications, compiler assumptions, hardware faults, and reality behaving unexpectedly](/assets/img/2026-10-23-Trust/formal-verification-policy.webp)

**Verification needn't promise bug-free software to be extraordinarily useful.** Anthropic's discoveries, repairs, and machine-checked guarantees are worth celebrating without demanding miracles.

I'm even more excited by the inverse question: beyond **using AI to make formal verification better**, how might we **use formal verification to make AI better?**

Instead of attaching a proof certificate at the end, imagine formal feedback helping AI learn, reason, catch mistakes, and generate better software—guided by independently meaningful specifications. Not just AI producing more proofs, but proofs helping AI improve.

![A loop of human intent, specifications, counterexamples, corrections, and verified feedback turning an error-prone AI into a more reliable one](/assets/img/2026-10-23-Trust/verification-helping-ai.webp)

This doesn't solve specification adequacy. An AI trained against the wrong objective might become spectacularly good at the wrong thing. **We've taught AI to optimize objectives. Perhaps we should spend more time worrying about who wrote them.**

The future isn't verifying everything indiscriminately. It's using verification where it gives meaningful assurance: safety-critical properties, unknown vulnerabilities, and feedback that improves AI before its output reaches production.

One question has been occupying my own research: **as AI produces formal representations of our requests, how do we know they mean what we intended?** I find that as interesting as proving them. Making guarantees more meaningful may matter as much as making proofs cheaper.

I hope to have more to share on that front soon. For now, let's just say that **proving the right thing might be a more interesting problem than proving things right.**

Ken Thompson's warning remains relevant four decades later. We can push the boundaries of what we prove, shrink our trusted computing bases, and make remarkable progress toward trustworthy software. But somewhere, whether in our specifications, our tools, our hardware, or our understanding of human intent, trust remains.

**Trust is not a failure of verification. Pretending that verification has eliminated the need for trust is.**
