---
layout: post
title: A Language-Agent Approach To Formal Theorem-Proving
subtitle: How can in-Context Learning help in proving theorems?
share-img: /assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/thumbnail.png
thumbnail-img: /assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/thumbnail.png
gh-repo: trishullab/copra
gh-badge: [star, fork, follow]
tags: [ML, Machine Learning, Generative AI, Prompt Engineering, GPTs, GPT-3.5, ChatGPT, GPT-4, AI, Artificial Intelligence, Language Agents, In-Context Learning, Prompting, Theorem Proving, Automatic Theorem Proving, Formal Theorem Proving, Formal Methods, Formal Verification, Coq, Lean]
comment_issue_id: 4
---
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/4.7.0/css/font-awesome.min.css">
  <link rel="stylesheet"
  href="https://cdn.jsdelivr.net/gh/jpswalsh/academicons@1/css/academicons.min.css">

  <!-- Github link -->
<a href="https://github.com/trishullab/copra" target="_blank"
    class="external-link button is-normal is-rounded is-dark"> <button style="font-size:24px">Code<i class="fa fa-github"></i></button>
</a>

<!--arXiv Link-->
<a href="https://arxiv.org/abs/2310.04353" target="_blank"
    class="external-link button is-normal is-rounded is-dark"> <button style="font-size:24px">arXiv<i class="ai ai-arxiv"></i></button>
</a>

## 1. What is Formal Theorem Proving ?

Writing rigorous proofs has always been a challenging task that lies at the core of Mathematics. However, with theorems getting more and more complex, it takes months if not years to verify handwritten (informal) proofs. This challenge opens up a new window for automation by writing proofs and verifying proofs in a [formal way](https://en.wikipedia.org/wiki/Formal_proof). Besides mathematics, there are many more applications for writing formal proofs including the writing of certified programs in situations where we want a correctness guarantee for software.

However, writing proofs formally has been a daunting task given the amount of verbosity needed for it to be verifiable by a machine. It takes years' worth of human work to write formal proofs. For example, it took multiple human years to finish the proofs for [CompCert](https://en.wikipedia.org/wiki/CompCert) which is a verified compiler for C language. Despite all the difficulties involved, people have started moving towards writing formal proofs using [proof assistants or Interactive Theorem Provers (ITPs)](https://en.wikipedia.org/wiki/Proof_assistant). These are software tools designed to help humans write verbose proofs in a verifiable language. However, even with these assistants, it is too cumbersome to write complex proofs in formal languages. This makes it absolutely necessary to automate this task or at least provide greater assistance to humans who are writing such formal proofs.


There are multiple languages for theorem proving like [Coq](https://en.wikipedia.org/wiki/Coq), [Lean](https://en.wikipedia.org/wiki/Lean_(proof_assistant)), [Isabelle](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant)), [ACL2](https://en.wikipedia.org/wiki/ACL2), etc.

```lean3
theorem mod_arith_2
(x : N) : x % 2 = 0 → (x * x) % 2 = 0 :=
begin
  intro h,
  rw nat.mul_mod,
  rw h,
  rw nat.zero_mul,
  refl,
end
```

>The figure above shows an example of proof written in [Lean 3](https://en.wikipedia.org/wiki/Lean_(proof_assistant)). This is a proof of the fact that for all natural numbers $x$, if $x$ is even then $x^2$ is also even.

```coq
(* Natural number definition. As per the definition, 3 = (S (S (S O)) *)
Inductive N : Set :=  O : N  (*Zero is a natural number*)
| S : N -> N. (*S is a function that returns the next natural number *)
(* addition over two natural numbers is defined recursively *)
Fixpoint add (n m : N) : N :=  match n with  
  | O => m  (* base case *)
  | S n_minus_one => S (add n_minus_one m)  (* recursive case *)
end.
(* Adding a natural number to zero gives back the same natural number *)
Theorem add_n_O : forall n : N, add n O = n.
Proof.
(*[Goal]<forall n : N, add n O = n>*)
intros n.
(*[NextGoal]<add n O = n>*)

(*[Goal]<add n O = n>*)
induction n.
(*[NextGoal]<add O O = O>*)

(*[Goal]<add O O = O>*)
simpl.
(*[NextGoal]<O = O>*)

(*[Goal]<O = O>*)
reflexivity.
(*[NextGoal]<add (S n) O = S n>*)

(*[Goal]<add (S n) O = S n>*)
simpl.
(*[NextGoal]<S (add n O) = S n>*)

(*[Goal]<S (add n O) = S n>*)
rewrite -> IHn.
(*[NextGoal] <S n = S n> *)

(*[Goal]<S n = S n> *)
reflexivity.
(*[NextGoal]<Proof finished>*)
Qed.
```

>The figure above shows a formal proof written in [Coq](https://en.wikipedia.org/wiki/Coq) language, and how the proof goal changes with application of each [proof-tactic](https://coq.inria.fr/refman/proof-engine/tactics.html). This also shows the formalization of natural numbers and a simple proof of the fact that for all natural numbers $n$, $n + 0 = n$.

## 2. Automatic Theorem Proving History

### 2.1 Proof Theory: Brief History

The proof theory tries to represent proofs as formal mathematical objects which can then be analyzed using mathematical tools. The formalization of proofs was first attempted by David Hilbert and Paul Bernays in their book called "[Grundlagen der Mathematik](https://en.wikipedia.org/wiki/Grundlagen_der_Mathematik)" in 1934-36. However, the mechanization of proofs was not successfully attempted until the 1970s when [Nqthm](https://en.wikipedia.org/wiki/Nqthm) was created by Boyer and Moore. Nqthm was the precursor to [ACL2](https://en.wikipedia.org/wiki/ACL2). ACL2 has been widely used in the industry, for example, by AMD to verify the correctness of floating-point operations. Later in the twenty-first century, more sophisticated proof languages like [Coq](https://en.wikipedia.org/wiki/Coq) and [Lean](https://en.wikipedia.org/wiki/Lean_(proof_assistant)) were developed. 



### 2.1 Automation and ITPs

Since we can express proofs in a formal language, it seems natural to describe the problem of proving as a search problem. The search space is the set of all possible proofs which can be written in this formal language. However, the search space is too large to be explored by a human. This is where automation comes into the picture. Automation can be used to explore the search space and find proofs. This is the idea behind [Automated Theorem Proving (ATP)](https://en.wikipedia.org/wiki/Automated_theorem_proving).

### 2.2 ATP and Machine Learning:
Given the vast space of possible proofs in formal language. It seems reasonable to use ML to narrow down the search space for finding proofs. We can categorize the work done in this field into the following categories:

- **Guided Proof Search**
  - **Train for Next Proof-Step Prediction + Search for sequence of proof-steps**: These approaches use supervised learning for predicting the next-proof step and then use this trained model to guide a search technique, e.g., best-first or depth-limited search, that synthesizes a proof. These methods were first based off on small slace neural networks ([Yang & Deng, 2019](https://arxiv.org/abs/1905.09381); [Sanchez-Stern et al., 2020](https://arxiv.org/abs/1907.07794); [Huang et al., 2019](https://arxiv.org/abs/1806.00608)) as predictors. More recent methods, such as GPT-f ([Polu & Sutskever, 2020](https://arxiv.org/abs/2009.03393)), PACT ([Han et al., 2021](https://arxiv.org/abs/2102.06203)), HyperTree Proof Search ([Lample et al., 2022](https://arxiv.org/abs/2205.11491)), and REPROVER ([Yang et al., 2023](https://arxiv.org/abs/2306.15626)), have used LLMs.
  - **Proof prediction using informal proofs**: The approach Draft-Sketch-Proof ([Jiang et al., 2022](https://arxiv.org/abs/2210.12283)) method relies on informal proofs to generate formal proofs.
  - **Proof prediction using error signals**: Methods like Baldur ([First et al., 2023](https://arxiv.org/abs/2303.04910)) generate the whole proof in one shot using an LLM and then repair it.
- **End-to-End Proof Search**: These methods use reinforcement learning to directly search for proofs. [Kaliszyk et al. (2018)](https://arxiv.org/abs/1805.07563) pioneered the use of RL in theorem-proving; subsequently, [Wu et al. (2021)](https://arxiv.org/abs/2102.09756) gave TacticZero, a deep RL approach to the problem.

### 2.3. Use of LLMs as Language Agents
Several distinct LLM agent architectures have been proposed over the last year ([AutoGPT](https://github.com/Significant-Gravitas/AutoGPT); [ReAct by Yao et al., 2022](https://arxiv.org/abs/2210.03629); [Reflection by Shinn et al., 2023](https://arxiv.org/abs/2303.11366); [Voyager by Wang et al., 2023](https://arxiv.org/abs/2305.16291)). These models
combine an LLM’s capability to use tools [(Toolformer by Schick et al. (2023))](https://arxiv.org/abs/2302.04761), decompose tasks into subtasks, and self-reflect. 

## 4. CoPrA: in-COntext PRover Agent

We introduce a new approach [in-**Co**ntext **Pr**over **A**gent (COPRA)](https://trishullab.github.io/copra/) which is a Language Agent for ATP. 

![CoPraOverview](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/copra_overview.png)

>The image above shows how our approach works. We propose a novel theorem proving agent which uses history of previous proof states, failures, repository of useful lemmas, and LLM as part of a verbal policy to predict the next proof action which will lead to simplification of the proof-state. Full details of our approach is described in our paper [A Language-Agent Approach To Formal Theorem-Proving (CoPrA)](https://arxiv.org/abs/2310.04353).


>(On a side-note: Copra actually means the dried, white flesh of the coconut from which coconut oil is extracted)

### 4.1 Approach

Our approach is based on the following ideas:
1. Use a stack to store the history of proof states and proof actions.
2. Have a map for storing a map of proof states to bad proof actions.
3. A Prompt Serialization Protocol (PSP) helps in laying out the history of proof actions, proof states, and textual rewards.

![Prompt Serialization Protocol](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/copra_prompts.png)

>In the above figure, Seq #1-#4 represent distinct invocations of the LLM. In each invocation, PSP first generates the “agent prompt,” which consists of three parts. The first part (“state”) is simply a serialization of the current proof state. The second (“stack”) incorporates information about previous actions as well as the bad actions for the current proof state. The third (“reward”) encodes the feedback from the environment regarding the success or failure of the last action. The
response of the LLM to this prompt is then translated into a proof action. This action is then executed on the theorem prover.

### 4.2 Evaluation

We evaluated our approach on two datasets: [miniF2F](https://github.com/facebookresearch/miniF2F) and [CompCert](https://github.com/UCSD-PL/proverbot9001/blob/master/compcert_projs_splits.json) which belong to different domains mathematics and software verification respectively.

We use a metric called ***"Pass@k-inference"*** while comparing our approach with [ReProver](https://arxiv.org/abs/2306.15626) and [Proverbot9001](https://arxiv.org/abs/1907.07794). The standard metric for evaluating theorem-provers is pass@k. In this metric, a prover is given a budget of k proof attempts; the
method is considered successful if one of these attempts leads to success. However, a key objective
of our research is to discover proofs quickly, with fewer LLM queries and lower wall-clock time.
The pass@k metric does not evaluate this characteristic as it does not quantify the number of LLM
queries or amount of time needed by a proof attempt. 

![CoPraEvaluation](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/miniF2F_pass_k_inference.png)
> The figure shows, comparison between ReProver and our approach on miniF2F dataset. The figure shows the number of proofs solved by CoPrA and ReProver as a function of the number of inference steps. CoPrA proves a lot more theorems in just 60 inference steps.

![CoPraEvaluation](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/compcert_pass_k_inferences.png)
> The figure shows, comparison between Proverbot9001 and our approach on CompCert dataset. The figure shows the number of proofs solved by CoPrA and Proverbot9001 as a function of the number of inference steps. CoPrA proves a lot more theorems in just 60 inference steps.

The tables below show a detailed comparison of our approach with ReProver and Proverbot9001.

![CoPraEvaluation](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/table1_pass@k_inferences.png)

![CoPraEvaluation](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/table2_wall_clock_times.png)

![CoPraEvaluation](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/table3_ablation.png)

From Table 3, we can see that backtracking is important for proving longer theorems. From these tables, it is clear that our approach is not able to find the proofs fast, but also give up proving much faster when the theorem is hard enough.

### 4.3 Some interesting proofs found by CoPrA

![CoPraEvaluation](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/copra_lean_proofs.png)
>The above image shows, some proofs in Lean found by CoPrA on miniF2F dataset.

![CoPraEvaluation](/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/copra_coq_proofs.png)
>The above image shows, some proofs in Coq found by CoPrA on CompCert dataset.