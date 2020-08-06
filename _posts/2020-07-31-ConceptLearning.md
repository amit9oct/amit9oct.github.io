---
layout: post
title: Concept Learning
subtitle: Machine Learning as a Search Problem
gh-repo: amit9oct/Tom-Mitchell-Notebook/
gh-badge: [star, fork, follow]
tags: [ML, Machine Learning, Concept Learning]
comments: true
---

# Concept Learning As Search
## 1.1 Introduction:
Concept learning can be viewed as a task to search through a large space of hypothesis that best fits the training examples.
Here we view learning as a searching problem, we examine different strategies to search the hypothesis space effectively.
## 1.2 General-to-Specific Ordering of Hypotheses
Consider the following example:

*Example 1.2.1:*
- Instances X: Possible days, each described by the attributes
    - Sky (*Sunny*, *Cloudy*, and *Rainy*)
    - AirTemp (*Warm* and *Cold*)
    - Humidity (*Normal* and *High*)
    - Wind (*Strong* and *Weak*)
    - Water (*Warm* and *Cool*)
    - Forecast (*Same* and *Change*)
- Hypothesis H: each hypothesis is described by a conjunction of constraints on the attributes *Sky, AirTemp, Humidity, Wind, Water* and *Forecast*. The constraints may be "?" (any value acceptable) "$\phi$" (no value acceptable) or a specific value.
- Target concept $c:EnjoySports: X \rightarrow \{0,1\}$
- Training examples D: Positive and negative examples of the target function

|Example|Sky|AirTemp|Humidity|Wind|Water|Forecast|EnjoySport|
|-|-----|----|------|------|----|----|---|
|1|Sunny|Warm|Normal|Strong|Warm|Same|Yes|
|2|Sunny|Warm|High|Strong|Warm|Same|Yes|
|3|Rainy|Cold|High|Strong|Warm|Same|No|
|4|Sunny|Warm|High|Strong|Cool|Change|Yes|

The **inductive learning hypothesis** states that any hypothesis found to approximate the target function well over a sufficiently large set of training examples will also approximate the target function well over other unobserved examples.

In *Example 1.2.1* the number of different hypothesis which can be generated without using *?* or *$ \phi $* are $3.2.2.2.2.2 = 96$, adding the two symbol gives us $5.4.4.4.4.4 = 5120$ syntactically distinct hypothesis. But if any hypothesis consisting of one or more $\phi$ symbols represents empty set of instance; that is, it classifies every instance as negative. Therefore, the number of semantically distinct hypotheses is only $1 + (4.3.3.3.3.3) = 973$. *EnjoySport* example is a very simple learning task, with a relatively small, finite hypothesis space.

Consider two hypothesis,<br>
$$h_1 = \;<Sunny, ?, ?, Strong, ?, ?> $$
$$h_2 = \;<Sunny, ?, ?, ?, ?, ?>$$
Clearly $h_2$ is more general than $h_1$ and $h_1$ is more specific.<br>
<br>
In general,<br>

<p> <b>Definition:</b> Let $h_j$ and $h_k$ be two boolean-valued functions defined over $X$. Then $h_j$ is <b>more general than or equal to</b> $h_k$ (written $h_j \ge_g h_k$) if and only if
$$(\forall x \in X) \;[(h_k(x) = 1) \rightarrow (h_j(x) = 1) ]$$</p>

\#Note: We can define inverse of the above as well.

## 1.3 Find-S

*Algorithm 1.3.1:* ***Find-S***

---
1. Initialize $h$ to the most specific hypothesis in $H$. The most specific hypothesis will be something like $<\phi, \phi, \dots, \phi>$
2. For each positive training instance $x$ :
    - For each attribute constrains $a_i$ in $h$:
        - **If** the constraint $a_i$ is satisfied by $x$ <br>
        - **Then** do nothing
        - **Else** replace $a_i$ in $h$ by next more general constraint that is satisfied by $x$
3. Output hypothesis $h$

---

### 1.3.1 Problems with Find-S

Although ***Find-S*** is simple and guaranteed to output a hypothesis with satisfying all positive examples. But it is not good in many practical cases because of multiple reasons:

- There is no way to determine whether the learned hypothesis is the only correct hypothesis. The ideal learning algorithm should determine whether it converged or not.
- *Find-S* prefers most specific hypothesis. There are multiple hypothesis possible but *Find-S* always choses the most specific one.
- The training example has to be consistent in order for *Find-S* to work.
- If there exists multiple hypothesis which are maximally specific which one to select.



```python
# Find-S implementation

import typing
class Hypothesis:
    def __init__(self, attributes: typing.List[str], possible_values: typing.Dict):
        self.attr = attributes
        self.possible_values = possible_values
        self.hypothesis_dict = [(attr, "\\phi") for attr in self.attr]
        assert all(attr in self.possible_values for attr in self.attr)
        for attr_values in self.possible_values.values():
            attr_values.append("?")
            attr_values.append("\\phi")
    
    def satisfies(self, attr_idx, x_value):
        attr, value = self.hypothesis_dict[attr_idx]
        if value == "\\phi":
            return False
        elif value == "?":
            return True
        else:
            return value == x_value
    
    def __str__(self):
        return "<{}>".format(", ".join(["\"{}\": \'{}\'".format(p[0], p[1]) for p in self.hypothesis_dict]))
    
    
def find_s(attributes: typing.List[str], possible_values: typing.Dict, examples: typing.List[str]):
    assert len(examples) > 0
    feature_count = len(attributes)
    assert all(len(example) == feature_count + 1 for example in examples)
    h = Hypothesis(attributes, possible_values)
    examples = [example for example in examples if example[feature_count]]
    for example in examples:
        for idx, attr in enumerate(attributes):
            if not h.satisfies(idx, example[idx]):
                attr_prev, value = h.hypothesis_dict[idx]
                h.hypothesis_dict[idx] = (attr, "?" if value != "\\phi" else example[idx])
    return h

attributes = ["Sky", "AirTemp", "Humidity", "Wind", "Water", "Forecast"] 
possible_values = {
    "Sky": ["Sunny", "Cloudy", "Rainy"],
    "AirTemp": ["Warm", "Cold"],
    "Humidity": ["Normal", "High"],
    "Wind": ["Strong", "Weak"],
    "Water": ["Warm", "Cold"],
    "Forecast": ["Same", "Change"]
}
data1 = [["Sunny", "Warm", "Normal", "Strong", "Warm", "Same", True], 
        ["Sunny", "Warm", "High", "Strong", "Warm", "Same", True],
        ["Rainy", "Cold", "High", "Strong", "Warm", "Same", False], 
        ["Sunny", "Warm", "High", "Strong", "Cool", "Change", True]]

data2 = [["Sunny", "Warm", "High", "Strong", "Warm", "Same", True], 
        ["Sunny", "Warm", "High", "Strong", "Warm", "Same", True],
        ["Rainy", "Cold", "High", "Strong", "Warm", "Change", False], 
        ["Sunny", "Warm", "High", "Strong", "Warm", "Same", True]]

data3 = [["Sunny", "Warm", "Normal", "Strong", "Cool", "Same", True], 
        ["Sunny", "Warm", "High", "Strong", "Warm", "Same", True],
        ["Rainy", "Cold", "High", "Strong", "Cool", "Change", False], 
        ["Rainy", "Warm", "High", "Strong", "Warm", "Same", True]]

h1 = find_s(attributes, possible_values, data1)
h2 = find_s(attributes, possible_values, data2)
h3 = find_s(attributes, possible_values, data3)
print(h1)
print(h2)
print(h3)
```

    <"Sky": 'Sunny', "AirTemp": 'Warm', "Humidity": '?', "Wind": 'Strong', "Water": '?', "Forecast": '?'>
    <"Sky": 'Sunny', "AirTemp": 'Warm', "Humidity": 'High', "Wind": 'Strong', "Water": 'Warm', "Forecast": 'Same'>
    <"Sky": '?', "AirTemp": 'Warm', "Humidity": '?', "Wind": 'Strong', "Water": '?', "Forecast": 'Same'>
    

## 1.3 Version Spaces and Candidate Elimination Algorithm

The main difference between *Find-S* and *Candidate Elimination Algorithm* is that it outputs *all hypothesis which are consistent with the training example*. *Candidate Elimination Algorithm* also uses same ***more general than*** partial ordering as *Find-S* but uses a compact representation to represent the hypothesis.

The CANDIDATE-ELIMINATION algorithm has been applied to problems such as learning regularities in chemical mass spectroscopy (Mitchell 1979) and learning control rules for heuristic search (Mitchell et al. 1983). Nevertheless, practical applications of the CANDIDATE-ELIMINATION and FIND-S algorithms are limited by the fact that they both perform poorly when given noisy training data.

### 1.3.1 Version Spaces
We use the ordered pair $<x, c(x)>$ to describe a training example consisting of the instance $x$ and it's target concept value $c(x)$.

***Definition:*** A hypothesis is consistent with a set of training examples $D$ if and only if $h(x) = c(x)$ for each example $<x, c(x)>$ in $D$.
$$Consistent(x, D) = (\;\forall <x,c(x)> \;\in D\;)\;h(x) = c(x)$$

***Definition:*** A ***version space*** with respect to a training example set $D$ and a hypothesis space $H$, denoted by $V_{HD}$, is subset of $H$ with all hypothesis which are consistent with the training examples in $D$.
$$V_{HD} = \{h \in H| \;Consistent(h, D)\}$$

### 1.3.2 List-Then-Eliminate

*Algorithm 1.3.2:* ***List-Then-Eliminate***

---
1. *VersionSpace* $\leftarrow$ a list containing all the hypothesis in $H$.
2. For each training example $<x, c(x)>\;\in\;D$
    - remove from *VersionSpace* any hypothesis *h* which for which $h(x) \ne c(x)$
3. Output the list of hypothesis in *VersionSpace*

---

Clearly this is a very simple way of searching through *Version Space*. Here the *Version Space* is represented by using a *list*. But there ways to represent *Version Space* in a more compact way.

### 1.3.3 Compact Representation of Version Space




#### 1.3.3.1 General Boundary

**Definition** : ***General Boundary*** with respect to a hypothesis space *H* and training set *D* is the set of maximally general members of hypothesis space *H* which are consistent with the training set *D*.

More mathematically,
$$G = \{g \in H: Consistent(g, D) \land (\neg\exists g' \in H)[g' >_{g} g] \} $$

#### 1.3.3.2 Specific Boundary

**Definition** : ***Specific Boundary*** with respect to a hypothesis space *H* and training set *D* is the set of maximally specific members of hypothesis space *H* which are consistent with the training set *D*.

More mathematically,
$$S = \{s \in H: Consistent(g, D) \land (\neg\exists s' \in H)[s >_{g} s'] \} $$

#### 1.3.3.3 Version Space Theorem

---
Let $X$ be an arbitrary set of instances and let $H$ be the set of all boolean-valued hypothesis defined over $X$. Let $c : X \rightarrow \{0, 1\}$ be a target concept defined over $X$, and let $D$ be an arbitrary set of training examples $\{<x,c(x)>\}$. For all X, H, c and D such that S and G are well defined:
$$VS_{H,D} = \{h \in H: (\exists s \in S)(\exists g \in G)(g \ge_g h \ge_g s)\}$$

**Proof Outline:**
We know that:
$$VS_{H,D} = \{h \in H: Consistent(h, D)\}$$
Also let,
$$T = \{h \in H: (g \exists G)(s \exists S)(g >_g h >_g s)\}$$
In order to prove this we will try proving $\forall h \in VS_{H,D} \rightarrow h \in T$ and vice-versa.
Let 

$h \in VS_{H,D}$

$h \in VS_{H,D} \rightarrow Consistent(h, D)$

**Lemma 1**: $(\forall h \in H \land Consistent(h, D) \land (\neg \exists g \in G)(g >_g h)) \rightarrow h \in G$

**Proof Lemma 1**:

Given, $h \in H \land Consistent(h, D)$,

$(\neg \exists g \in G)(g >_g h)$

$\implies (\neg \exists g' \in H)(\neg \exists g \in G)(g' >_g g \land g >_g h)$

$\implies (\neg \exists g' \in H)(\neg \exists g \in G)(g' >_g g >_g h)$

$\implies (\neg \exists g' \in H)(g' >_g h)$

$\implies h \in G$

**Lemma 2**: $(\forall h \in H \land Consistent(h, D) \land (\neg \exists s \in S)(h >_g s)) \rightarrow h \in S$

**Proof Lemma 2**:

Similar to *Lemma 1* proof.

**Main Proof:**

If $h \in S$ the proof is  trivial and similarly $h \in G$ the proof is trivial. (Think why!!)

If $(h \in H) \land (h \not\in S) \land (h \not\in G)$ then use *Lemma 1* and *Lemma 2* to prove that $h \in T$

Given $h \in T$,

$\implies (\exists g \in G)(\exists s \in S)(g \ge_g h \ge_g s)$

$\implies (\exists g \in G)(\exists s \in S)(g \ge_g h \ge_g s)$

Now $h \ge_g s \rightarrow h$ satisfies all positive examples of $D$ also $g \ge_g h \rightarrow h$ satisfies all negative examples of $D$

$\implies Consistent(h, D)$

$\implies h \in VS_{H,D}$

---

### References and Reading

- This page is generated from the following Jupyter Notebook: [ConceptLearning.ipynb](https://github.com/amit9oct/Tom-Mitchell-Notebook/blob/master/Chapter2/ConceptLearning.ipynb) . 
- This blog is heavily influenced by Tom Mitchell's [Machine Learning book](https://www.cs.ubbcluj.ro/~gabis/ml/ml-books/McGrawHill%20-%20Machine%20Learning%20-Tom%20Mitchell.pdf)