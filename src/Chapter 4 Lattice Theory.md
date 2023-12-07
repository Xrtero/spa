# Chapter 4 Lattice Theory

The technique for static analysis that we will study next is based on the mathematical theory of _lattices_, which we briefly review in this chapter. The connection between lattices and program analysis was established in the seminal work by Kildall, Kam and Ullman [12, 13].

## 4.1 Motivating Example: Sign Analysis

As a motivating example, assume that we wish to design an analysis that can find out the possible signs of the integer values of variables and expressions in a given program. In concrete executions, values can be arbitrary integers. In contrast, our analysis considers an abstraction of the integer values by grouping them into the three categories, or _abstract values_: positive (+), negative (-), and zero (0). Similar to the analysis we considered in Chapter 3, we circumvent undecidability by introducing approximation. That is, the analysis must be prepared to handle uncertain information, in this case situations where it does not know the sign of some expression, so we add a special abstract value ($\top$) representing "don't know". We must also decide what information we are interested in for the cases where the sign of some expression is, for example, positive in some executions but not in others. For this example, let us assume we are interested in _definite_ information, that is, the analysis should only report + for a given expression if it is certain that this expression will evaluate to a positive number in _every_ execution of that expression and $\top$ otherwise. In addition, it turns out to be beneficial to also introduce an abstract value $\bot$ for expressions whose values are not numbers (but instead, say, pointers) or have no value in any execution because they are unreachable from the program entry.

Consider this program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171629562.png)
Here, the analysis could conclude that a and b are positive numbers in all possible executions at the end of the program. The sign of c is either positive or negative depending on the concrete execution, so the analysis must report $\top$ for that variable.

For this analysis we have an _abstract domain_ consisting of the five abstract values $\{+,\_,\emptyset,\top,\bot\}$, which we can organize as follows with the least precise information at the top and the most precise information at the bottom:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171629813.png)

The ordering reflects the fact that $\bot$ represents the empty set of integer values and $\top$ represents the set of all integer values. Note that $\top$ may arise for different reasons: (1) In the example above, there exist executions where c is positive and executions where c is negative, so, for this choice of abstract domain, $\top$ is the only sound option. (2) Due to undecidability, imperfect precision is inevitable, so no matter how we design the analysis there will be programs where, for example, some variable can only have a positive value in any execution but the analysis is not able to show that it could not also have a negative value (recall the TM(j) example from Chapter 1).

The five-element abstract domain shown above is an example of a so-called complete lattice. We continue the development of the sign analysis in Section 5.1, but we first need the mathematical foundation in place.

## 4.2 Lattices

A _partial order_ is a set $S$ equipped with a binary relation $\sqsubseteq$ where the following conditions are satisfied:
* reflexivity: $\forall x\in S\colon x\sqsubseteq x$
* transitivity: $\forall x,y,z\in S\colon x\sqsubseteq y\,\land\,y\sqsubseteq z\implies x\sqsubseteq z$
* anti-symmetry: $\forall x,y\in S\colon x\sqsubseteq y\,\land\,y\sqsubseteq x\implies x=y$The abstract domain shown in Section 4.1 is an example of a partial order, where $S=\{\neg,\emptyset,+,\top,\bot\}$ and $\sqsubseteq$ specifies the ordering of the elements, for example, $\bot\sqsubseteq$ + and + $\sqsubseteq\top$.

The abstract domain shown in Section 4.1 is an example of a partial order, where $S=\{-, \boldsymbol{\theta},+, \top, \perp\}$ and $\sqsubseteq$ specifies the ordering of the elements, for example, $\perp \sqsubseteq+$ and $+\sqsubseteq \top$.

When $x \sqsubseteq y$ we say that y is a safe approximation of $x$, or that $x$ is at least as precise as y. Formally, a partial order is a pair ($S, \sqsubseteq$), but we often use the same name for the partial order and its underlying set S. Also, we sometimes write $y \sqsupseteq x$ (" y is greater than or equal $x^{\prime \prime}$ ) instead of $x \sqsubseteq y$ (" $x$ is less than or equal $y$ ") .

Let $X \subseteq S$. We say that $y \in S$ is an upper bound for $X$, written $X \sqsubseteq y$, if we have $\forall x \in X$: $x \sqsubseteq y$. Similarly, $y \in S$ is a lower bound for X, written $y \sqsubseteq X$, if $\forall x \in X$: $y \sqsubseteq x$. A least upper bound, written $\bigsqcup X$, is defined by:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171633293.png)


Dually, a _greatest_ lower bound, written $\sqcap X$, is defined by:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171644059.png)

For pairs of elements, we sometimes use the infix notation $x\sqcup y$ (called the _join_ of $x$ and $y$) instead of $\bigsqcup\{x,y\}$ and $x\sqcap y$ (called the _meet_ of $x$ and $y$) instead of $\sqcap\{x,y\}$.

We also sometimes use the subscript notation, for example writing $\bigsqcup_{a\in A}f(a)$ instead of $\bigsqcup\{f(a)\mid a\in A\}$.

The least upper bound operation plays an important role in program analysis. As we shall see in Chapter 5, we use least upper bound when combining abstract information from multiple sources, for example when control flow merges after the branches of if statements.

**Exercise 4.1**: Let $X\subseteq S$. Prove that if $\bigsqcup X$ exists, then it must be unique. (A similar argument shows that the same property holds for greatest lower bounds: if $\sqcap X$ exists, then it must be unique.)

**Exercise 4.2**: Prove that if $x\sqcup y$ exists then $x\sqsubseteq y\iff x\sqcup y=y$, and conversely, if $x\sqcap y$ exists then $x\sqsubseteq y\iff x\sqcap y=x$.

A _lattice_ is a partial order $(S,\sqsubseteq)$ in which $x\sqcup y$ and $x\sqcap y$ exist for all $x,y\in S$. A _complete lattice_ is a partial order $(S,\sqsubseteq)$ in which $\bigsqcup X$ and $\sqcap X$ exist for all $X\subseteq S$. Trivially, every complete lattice is a lattice. Most lattices we encounter in program analysis are complete lattices.

**Exercise 4.3**: Argue that the abstract domain presented in Section 4.1 is a complete lattice.

**Exercise 4.4**: Prove that if $(S,\sqsubseteq)$ is a nonempty finite lattice (i.e., a lattice where $S$ is nonempty and finite), then $(S,\sqsubseteq)$ is also a complete lattice.

**Exercise 4.5**: Give an example of a nonempty lattice that is not a complete lattice.

Any finite partial order may be illustrated by a Hasse diagram in which the elements are nodes and the order relation is the transitive closure of edges leading from lower to higher nodes. With this notation, all of the following partial orders are also lattices:

![](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171648795.png)

whereas these partial orders are _not_ lattices:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171648126.png)

**Exercise 4.6**: Why do these two diagrams not define lattices?

It follows from the following exercise that to show that a partial order is a complete lattice, it suffices to argue that a least upper bound exists for each subset of its elements; the presence of greatest lower bounds then comes for free (and the dual property also holds).

**Exercise 4.7**: Prove that if $S$ is a partially ordered set, then every subset of $S$ has a least upper bound if and only if every subset of $S$ has a greatest lower bound. (Hint: )

Every complete lattice has a unique _largest_ element denoted $\top$ (pronounced _top_) and a unique _smallest_ element denoted $\bot$ (pronounced _bottom_).

**Exercise 4.8**: Assume $S$ is a partial order where $\bigsqcup S$ and $\sqcap S$ exist. Prove that $\bigsqcup S$ and $\sqcap S$ are the unique largest element and the unique smallest element, respectively, in $S$. In other words, we have $\top=\bigsqcup S$ and $\bot=\sqcap S$.

**Exercise 4.9**: Assume $S$ is a partial order where $\sqcup S$, $\sqcap S$, $\sqcup\emptyset$ and $\sqcap\emptyset$ exist. Prove that $\bigsqcup S=\sqcap\emptyset$ and that $\sqcap S=\sqcup\emptyset$. (Together with Exercise 4.8 we then have $\top=\sqcap\emptyset$ and $\bot=\sqcup\emptyset$.)The _height_ of a lattice is defined to be the length of the longest path from $\bot$ to $\top$. As an example, the height of the sign analysis lattice from Section 4.1 is $2$. For some lattices the height is infinite (see Section 6.1).

## 4.3 Constructing Lattices

Every set $A=\{a_{1},a_{2},\dots\}$ defines a complete lattice $(\mathcal{P}(A),\subseteq)$, where $\bot=\emptyset$, $\top=A$, $x\sqcup y=x\cup y$, and $x\sqcap y=x\cap y$. We call this the _powerset lattice_ for $A$. For a set with four elements, $\{0,1,2,3\}$, the powerset lattice looks like this:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171648338.png)

The above powerset lattice has height $4$. In general, the lattice $(\mathcal{P}(A),\subseteq)$ has height $|A|$. We use powerset lattices in Chapter 5 to represent sets of variables or expressions.

The _reverse powerset lattice_ for a set $A$ is the complete lattice $(\mathcal{P}(A),\supseteq)$.

**Exercise 4.10**: Draw the Hasse diagram of the reverse powerset lattice for the set $\{\mathtt{foo},\mathtt{bar},\mathtt{bar}\mathtt{bar}\}$.

If $A=\{a_{1},a_{2},\dots\}$ is a set, then $\mathit{flat}(A)$ illustrated by

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171648454.png)

is a complete lattice with height $2$. As an example, the set $\mathit{Sign}=\{\mathtt{+},\mathtt{-},\mathtt{\emptyset},\top,\bot\}$ with the ordering described in Section 4.1 forms a complete lattice that can also be expressed as $\mathit{flat}(\{\mathtt{+},\mathtt{\emptyset},\mathtt{-}\})$.

If $L_{1},L_{2},\ldots,L_{n}$ are complete lattices, then so is the _product_:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171649389.png)


where the order $\sqsubseteq$ is defined componentwise:[^f1]

[^f1]: We often abuse notation by using the same symbol $\sqsubseteq$ for many different order relations, in this case from the $n+1$ different lattices, but it should always be clear from the context which lattice it belongs to. The same applies to the other operators $\sqsupseteq$, $\sqcup$, $\sqcap$ and the top/bottom symbols $\top$, $\bot$.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171649588.png)

Products of $n$ identical lattices may be written concisely as $L^{n}=\underbrace{L\times L\times\ldots\times L}_{n}$.

**Exercise 4.11**: Show that the $\sqcup$ and $\sqcap$ operators for a product lattice $L_{1}\times L_{2}\times\ldots\times L_{n}$ can be computed componentwise (i.e. in terms of the $\sqcup$ and $\sqcap$ operators from $L_{1}$, $L_{2}$,..., $L_{k}$).

**Exercise 4.12**: Show that $\mathit{height}(L_{1}\times\ldots\times L_{n})=\mathit{height}(L_{1})+\ldots+ \mathit{height}(L_{n})$.

If $A$ is a set and $L$ is a complete lattice, then we obtain a complete lattice called a _map_ lattice consisting of the set of functions from $A$ to $L$, ordered pointwise:[^f2]

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171649271.png)

[^f2]: The notation $[a_{1}\mapsto x_{1},a_{2}\mapsto x_{2},\ldots]$ means the function that maps $a_{1}$ to $x_{1}$, $a_{2}$ to $x_{2}$, etc.


We have already seen that the set $\operatorname{Sign}=\{+,-, \mathbb{0}, \top, \perp\}$ with the ordering described in Section 4.1 forms a complete lattice that we use for describing abstract values in the sign analysis. An example of a map lattice is $StateSigns = Vars \rightarrow Sign$ where $Vars$ is the set of variable names occurring in the program that we wish to analyze. Elements of this lattice describe abstract states that provide abstract values for all variables. An example of a product lattice is $ProgramSigns = StateSigns { }^{n}$ where n is the number of nodes in the CFG of the program. We shall use this lattice, which can describe abstract states for all nodes of the program CFG, in Section 5.1 for building a flow-sensitive sign analysis. This example also illustrates that the lattices we use may depend on the program being analyzed: the sign analysis depends on the set of variables that occur in the program and also on its CFG nodes.

**Exercise 4.13**: Show that the $\sqcup$ and $\sqcap$ operators for a map lattice $A \rightarrow L$ can be computed pointwise (i.e. in terms of the $\sqcup$ and $\sqcap$ operators from $L$ ).

**Exercise 4.14**: Show that if A is finite and L has finite height then the height of the map lattice $A \rightarrow L is height (A \rightarrow L)=|A| \cdot \operatorname{height}(L)$.

If $L_{1}$ and $L_{2}$ are lattices, then a function f: $L_{1} \rightarrow L_{2}$ is a homomorphism if $\forall x, y \in L_{1}$: f$(x \sqcup y)=f(x) \sqcup f(y) \wedge f(x \sqcap y)=f(x) \sqcap f(y)$. A bijective homomorphism is called an isomorphism. Two lattices are isomorphic if there exists an isomorphism from one to the other.

**Exercise 4.15**: Argue that every product lattice $L^{n}$ is isomorphic to a map lattice $A\to L$ for some choice of $A$, and vice versa.

Note that by Exercise 4.15 the lattice $\mathit{StateSigns}^{n}$ is isomorphic to $\mathit{Nodes}\to\mathit{StateSigns}$ where $\mathit{Nodes}$ is the set of CFG nodes, so which of the two variants we use when describing the sign analysis is only a matter of preferences.


If $L$ is a complete lattice, then so is $\mathit{lift}(L)$, which is a copy of $L$ but with a new bottom element:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171653121.png)

It has $\mathit{height}(\mathit{lift}(L))=\mathit{height}(L)+1$ if $L$ has finite height. One use of lifted lattices is for defining the lattice used in interval analysis (Section 6.1), another is for representing reachability information (Section 8.2).

### 4.4 Equations, Monotonicity, and Fixed Points

Continuing the sign analysis from Section 4.1, what are the signs of the variables at each line of the following simple program?

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171654586.png)

We can derive a system of equality constraints (equations) with one constraint variable for each program variable and line number from the program:[^f3]


[^f3]: We use the term _constraint variable_ to denote variables that appear in mathematical constraint systems, to avoid confusion with _program variables_ that appear in TIP programs.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171654024.png)

For example, $a_{2}$ denotes the abstract value of a at the program point immediately after line 2. The operators + and - here work on abstract values, which we return to in Section 5.1. In this constraint system, the constraint variables have values from the abstract value lattice $Sign$ defined in Section 4.3. We can alternatively derive the following equivalent constraint system where each constraint variable instead has a value from the abstract state lattice $StateSigns$ from Section 4.3:[^f4]

[^f4]: The notation $f[a_{1}\mapsto x_{n},\ldots,a_{n}\mapsto x_{n}]$ means the function that maps $a_{i}$ to $x_{i}$, for each $i=1,\ldots,n$ and for all other inputs gives the same output as the function $f$.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171655654.png)

Here, each constraint variable models the abstract state at a program point; for example, $x_{1}$ models the abstract state at the program point immediately after line 1. Notice that each equation only depends on preceding ones for this example program, so in this case the solution can be found by simple substitution. However, mutually recursive equations may appear, for example for programs that contain loops (see Section 5.1).

Also notice that it is important for the analysis of this simple program that the order of statements is taken into account, which is called _flow-sensitive_ analysis. Specifically, when a is read in line 3, the value comes from the assignment to a in line 2, not from the one in line 4.

**Exercise 4.16**: Give a solution to the constraint system above (that is, values for $x_{1},\ldots,x_{4}$ that satisfy the four equations).

**Exercise 4.17**: Why is the unification solver from Chapter 3 not suitable for this kind of constraints?

We now show how to solve such constraint systems in a general setting.

A function $f\colon L_{1}\to L_{2}$ where $L_{1}$ and $L_{2}$ are lattices is _monotone_ (or _order-preserving_) when $\forall x,y\in L_{1}\colon x\sqsubseteq y\implies f(x)\sqsubseteq f(y)$. As the lattice order when used in program analysis represents precision of information, the intuition of monotonicity is that "more precise input does not result in less precise output".

**Exercise 4.18**: A function $f\colon L\to L$ where $L$ is a lattice is _extensive_ when $\forall x\in L\colon x\sqsubseteq f(x)$. Assume $L$ is the powerset lattice $\mathcal{P}(\{0,1,2,3,4\})$ Give examples of different functions $L\to L$ that are, respectively,

a. extensive and monotone,
b. extensive but not monotone,
c. not extensive but monotone, and
d. not extensive and not monotone.

**Exercise 4.19**: Prove that every constant function is monotone.

**Exercise 4.20**: A function $f\colon L_{1}\to L_{2}$ where $L_{1}$ and $L_{2}$ are lattices is _distributive_ when $\forall x,y\in L_{1}\colon f(x)\sqcup f(y)=f(x\sqcup y)$.

a. Show that every distributive function is also monotone.
b. Show that not every monotone function is also distributive.

**Exercise 4.21**: Prove that a function $f\colon L_{1}\to L_{2}$ where $L_{1}$ and $L_{2}$ are lattices is monotone if and only if $\forall x,y\in L_{1}\colon f(x)\sqcup f(y)\sqsubseteq f(x\sqcup y)$.

**Exercise 4.22**: Prove that function composition preserves monotonicity. That is, if $f\colon L_{1}\to L_{2}$ and $g\colon L_{2}\to L_{3}$ are monotone, then so is their composition $g\circ f$, which is defined by $(g\circ f)(x)=g(f(x))$.

The definition of monotonicity generalizes naturally to functions with multiple arguments: for example, a function with two arguments $f\colon L_{1}\times L_{2}\to L_{3}$ where $L_{1}$, $L_{2}$, and $L_{3}$ are lattices is monotone when $\forall x_{1},y_{1}\in L_{1},x_{2}\in L_{2}\colon x_{1}\sqsubseteq y_{1} \implies f(x_{1},x_{2})\sqsubseteq f(y_{1},x_{2})$ and $\forall x_{1}\in L_{1},x_{2},y_{2}\in L_{2}\colon x_{2}\sqsubseteq y_{2} \implies f(x_{1},x_{2})\sqsubseteq f(x_{1},y_{2})$.

**Exercise 4.23**: The operators $\sqcup$ and $\sqcap$ can be viewed as functions. For example, $x_{1}\sqcup x_{2}$ takes as input $x_{1},x_{2}\in L$ and returns an element from $L$ as output. Show that $\sqcup$ and $\sqcap$ are monotone.

**Exercise 4.24**: Let $f\colon L^{n}\to L^{n}$ be a function $n$ arguments over a lattice $L$. We can view such a function in different ways: either as function with $n$ arguments from $L$, or as a function with single argument from the product lattice $L^{n}$. Argue that this does not matter for the definition of monotonicity.

**Exercise 4.25**: Show that set difference, $X\backslash Y$, as a function with two arguments over a powerset lattice is monotone in the first argument $X$ but not in the second argument $Y$.

**Exercise 4.26**: Recall that $f[a\mapsto x]$ denotes the function that is identical to $f$ except that it maps $a$ to $x$. Assume $f\colon L_{1}\to(A\to L_{2})$ and $g\colon L_{1}\to L_{2}$ are monotone functions where $L_{1}$ and $L_{2}$ are lattices and $A$ is a set, and let $a\in A$. (Note that the codomain of $f$ is a map lattice.) Show that the function $h\colon L_{1}\to(A\to L_{2})$ defined by $h(x)=f(x)[a\mapsto g(x)]$ is monotone.

Also show that the following claim is _wrong_: The map update operation preserves monotonicity in the sense that if $f\colon L\to L$ is monotone then so is $f[a\mapsto x]$ for any lattice $L$ and $a,x\in L$.

We say that $x\in L$ is a _fixed point_ for $f$ if $f(x)=x$. A _least_ fixed point $x$ for $f$ is a fixed point for $f$ where $x\sqsubseteq y$ for every fixed point $y$ for $f$.

Let $L$ be a complete lattice. An _equation system_ [^f5] over $L$ is of the form

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171656615.png)

[^f5]: We also use the broader concept of _constraint systems_. An equation system is a constraint system where all constraint are equalities. On page 4.26 we discuss other forms of constraints.

where $x_{1},\ldots,x_{n}$ are variables and $f_{1},\ldots,f_{n}\colon L^{n}\to L$ are functions which we call _constraint functions_. A _solution_ to an equation system provides a value from $L$ for each variable such that all equations are satisfied.
We can combine the $n$ functions into one, $f\colon L^{n}\to L^{n}$,
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171657379.png)
in which case the equation system looks like

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171657010.png)

where $x\in L^{n}$. This clearly shows that a solution to an equation system is the same as a fixed point of its functions. As we aim for the most precise solutions, we want _least_ fixed points.

**Exercise 4.27**: Show that $f$ is monotone if and only if each $f_{1},\ldots,f_{n}$ is monotone, where $f$ is defined from $f_{1},\ldots,f_{n}$ as above.

As an example, for the equation system from earlier in this section

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171658377.png)

we have four constraint variables, $x_{1},\ldots,x_{4}$ with constraint functions $f_{1},\ldots,f_{4}$ defined as follows:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171658151.png)


**Exercise 4.28**: Show that the four constraint functions $f_{1},\ldots,f_{4}$ are monotone. (Hint: see Exercise 4.26.)

As mentioned earlier, for this simple equation system it is trivial to find a solution by substitution, however, that method is inadequate for equation systems that arise when analyzing programs more generally.

**Exercise 4.29**: Argue that your solution from Exercise 4.16 is the least fixed point of the function $f$ defined by
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171658613.png)

The central result we need is the following _fixed-point theorem_ due to Kleene [10]: [^f6]

[^f6]: The ordinary Kleene fixed-point theorem requires $f$ to be continuous (see page 4.16), on the other hand it does not require $L$ to be a complete lattice but it can be any complete partial order (possibly with infinite height); see also Exercise 4.28.

In a complete lattice L with finite height, every monotone function $f: L \rightarrow L$ has a unique least fixed point denoted $lfp(f)$ defined as:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171659653.png)

(Note that when applying this theorem to the specific equation system shown above, $f$ is a function over the product lattice $L^{n}$.)

The proof of this theorem is quite simple. Observe that $\bot\sqsubseteq f(\bot)$ since $\bot$ is the least element. Since $f$ is monotone, it follows that $f(\bot)\sqsubseteq f^{2}(\bot)$ and by induction that $f^{i}(\bot)\sqsubseteq f^{i+1}(\bot)$ for any $i$. Thus, we have an increasing chain:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171700180.png)

Since $L$ is assumed to have finite height, we must for some $k$ have that $f^{k}(\bot)=f^{k+1}(\bot)$, i.e. $f^{k}(\bot)$ is a fixed point for $f$. By Exercise 4.2, $f^{k}(\bot)$ must be the least upper bound of all elements in the chain, so $\mathit{lfp}(f)=f^{k}(\bot)$. Assume now that $x$ is another fixed point. Since $\bot\sqsubseteq x$ it follows that $f(\bot)\sqsubseteq f(x)=x$, since $f$ is  monotone, and by induction we get that $lfp(f)=f^{k}(\perp) \sqsubseteq x$. Hence, $lfp (f)$ is a least fixed point, and by anti-symmetry of $\sqsubseteq$ it is also unique.

The theorem is a powerful result: It tells us not only that equation systems over complete lattices always have solutions, provided that the lattices have finite height and the constraint functions are monotone, but also that uniquely most precise solutions always exist. Furthermore, the careful reader may have noticed that the theorem provides an algorithm for computing the least fixed point: simply compute the increasing chain $\perp \sqsubseteq f(\perp) \sqsubseteq f^{2}(\perp) \sqsubseteq \ldots$ until the fixed point is reached. In pseudo-code, this so-called naive fixed-point algorithm looks as follows.
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171720984.png)
(Instead of computing f(x) both in the loop condition and in the loop body, a trivial improvement is to just compute it once in each iteration and see if the result changes.) The computation of a fixed point can be illustrated as a walk up the lattice starting at $\perp$ :

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171721747.png)
This algorithm is called "naive" because it does not exploit the special structures that are common in analysis lattices. We shall see various less naive fixed-point algorithms in Section 5.3.

The least fixed point is the most precise possible solution to the equation system, but the equation system is (for a sound analysis) merely a conservative approximation of the actual program behavior (again, recall the $TM (j)$ example from Chapter 1 ). This means that the semantically most precise possible (while still correct) answer is generally below the least fixed point in the lattice. We shall see examples of this in Chapter 5 and study the connection to semantics in more detail in Chapter 12.



**Exercise 4.30**: Explain step-by-step how the naive fixed-point algorithm computes the solution to the equation system from Exercise 4.16.

The time complexity of computing a fixed point with this algorithm depends on

* the height of the lattice, since this provides a bound for the number of iterations of the algorithm, and
* the cost of computing $f(x)$ and testing equality, which are performed in each iteration.

We shall investigate other properties of this algorithm and more sophisticated variants in Section 5.3.

**Exercise 4.31**: Does the fixed-point theorem also hold without the assumption that $f$ is monotone? If yes, give a proof; if no, give a counterexample.

**Exercise 4.32**: Does the fixed-point theorem also hold without the assumption that the lattice has finite height? If yes, give a proof; if no, give a counterexample. (Hint: see [10].)

We can similarly solve systems of _inequations_ of the form

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171722886.png)


by observing that the relation $x\sqsupseteq y$ is equivalent to $x=x\sqcup y$ (see Exercise 4.2). Thus, solutions are preserved by rewriting the system into
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171722723.png)

which is just a system of equations with monotone functions as before (see Exercise 4.22 and 4.23). Conversely, constraints of the form

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171722359.png)

can be rewritten into
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171723992.png)


by observing that the relation $x\sqsubseteq y$ is equivalent to $x=x\sqcap y$.

In case we have multiple inequations for each variable, those can also easily be reorganized, for example

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171723178.png)

can be rewritten into

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171723871.png)

which again preserves the solutions.