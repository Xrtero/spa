# Chapter 5 Dataflow Analysis with Monotone Frameworks

Classical dataflow analysis starts with a CFG and a complete lattice with finite height. The lattice describes abstract information we wish to infer for the different CFG nodes. It may be fixed for all programs, or it may be parameterized based on the given program. To every node $v$ in the CFG, we assign a constraint variable[^f1]$[\![v]\!]$ ranging over the elements of the lattice. For each node we then define a _dataflow constraint_ that relates the value of the variable of the node to those of other nodes (typically the neighbors), depending on what construction in the programming language the node represents. If all the constraints for the given program happen to be equations or inequations with monotone right-hand sides, then we can use the fixed-point algorithm from Section 4.4 to compute the analysis result as the unique least solution.

[^f1]: As for type analysis, we will ambiguously use the notation $[\![S]\!]$ for $[\![v]\!]$ if $S$ is the syntax associated with node $v$. The meaning will always be clear from the context.

The combination of a complete lattice and a space of monotone functions is called a _monotone framework_[12]. For a given program to be analyzed, a monotone framework can be instantiated by specifying the CFG and the rules for assigning dataflow constraints to its nodes.

An analysis is _sound_ if all solutions to the constraints correspond to correct information about the program. The solutions may be more or less imprecise, but computing the least solution will give the highest degree of precision possible. We return to the topic of analysis correctness and precision in Chapter 12.

Throughout this chapter we use the subset of TIP without function calls, pointers, and records; those language features are studied in Chapters 10 and 11 and in Exercise 5.10.

## 5.1 Sign Analysis, Revisited

Continuing the example from Section 4.1, our goal is to determine the sign (positive, zero, negative) of all expressions in the given programs. We start with the tiny lattice $Sign$ for describing abstract values:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172007401.png)

We want an abstract value for each program variable, so we define the map lattice
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172007724.png)

where $\mathit{Vars}$ is the set of variables occurring in the given program. Each element of this lattice can be thought of as an abstract state, hence its name. For each CFG node $v$ we assign a constraint variable $[\![v]\!]$ denoting an abstract state that gives the sign values for all variables at the program point immediately after $v$. The lattice $\mathit{States}^{n}$, where $n$ is the number of CFG nodes, then models information for all the CFG nodes.

The dataflow constraints model the effects of program execution on the abstract states. For simplicity, we here focus on a subset of TIP that does not contain pointers or records, so integers are the only type of values we need to consider.

First, we define an auxiliary function $\mathit{JOIN}(v)$ that combines the abstract states from the predecessors of a node $v$:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172007374.png)

Note that $\mathit{JOIN}(v)$ is a function of all the constraint variables $[\![v_{1}]\!],\dots,[\![v_{n}]\!]$ for the program. For example, with the following CFG, we have $\mathit{JOIN}([\![\text{a=c+2}]\!])=[\![\text{c=b}]\!]\sqcup[\![\text{c=-5}]\!]$.
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172008895.png)

The most interesting constraint rule for this analysis is the one for assignment statements, that is, nodes $v$ of the form $X=E$:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172008965.png)

This constraint rule models the fact that the abstract state after an assignment $X=E$ is equal to the abstract state immediately before the assignment, except that the abstract value of $X$ is the result of abstractly evaluating the expression $E$. The $\mathit{eval}$ function performs an abstract evaluation of expression $E$ relative to an abstract state $\sigma$:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172008105.png)

The function $\mathit{sign}$ gives the sign of an integer constant, and $\hat{\mathit{op}}$ is an abstract evaluation of the given operator,2 defined by the following tables:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172008299.png)

Variable declarations are modeled as follows (recall that freshly declared
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172009744.png)
For the subset of TIP we have chosen to focus on, no other kinds of CFG nodes affect the values of variables, so for the remaining nodes we have this trivial constraint rule:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172010625.png)

**Exercise 5.1**: In the CFGs we consider in this chapter (for TIP without function calls), entry nodes have no predecessors.

1. Argue that the constraint rule $[\![ v ]\!]=JOIN(v)$ for such nodes is equivalent to defining $[\![ v ]\!] =\bot$.
2. Argue that removing all equations of the form $[\![ v ]\!]=\bot$ from an equation system does not change its least solution.

A program with $n$ CFG nodes, $v_{1},\ldots,v_{n}$, is thus represented by $n$ equations,

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172011482.png)

where $\mathit{af}_{v}\colon\mathit{States}^{n}\to\mathit{States}$ for each CFG node $v$.

The lattice and constraints form a monotone framework. To see that all the right-hand sides of our constraints correspond to monotone functions, notice that they are all composed (see Exercise 4.22) from the $\sqcup$ operator (see Exercise 4.23), map updates (see Exercise 4.26), and the $\mathit{eval}$ function. The $\mathit{sign}$ function is constant (see Exercise 4.19). Monotonicity of the abstract operators used by $\mathit{eval}$ can be verified by a tedious manual inspection. For a lattice with $n$ elements, monotonicity of an $n\times n$ table can be verified automatically in time $\mathcal{O}(n^{3})$.

**Exercise 5.2**: Describe an algorithm for checking monotonicity of an operator given by an $n\times n$ table. Can you do better than $\mathcal{O}(n^{3})$ time?

**Exercise 5.3**: Check that the above tables indeed define monotone operators on the $\mathit{Sign}$ lattice.

**Exercise 5.4**: Argue that these tables are the most precise possible for the $\mathit{Sign}$ lattice, given that soundness must be preserved. (An informal argument suffices for now; we shall see a more formal approach to stating and proving this property in Section 12.4.)

**Exercise 5.5**: The table for the abstract evaluation of == is unsound if we consider the full TIP language instead of the subset without pointers, function calls, and records. Why? And how could it be fixed?

Using the fixed-point algorithm from Section 4.4, we can now obtain the analysis result for the given program by computing $\mathit{lfp}(\mathit{af})$ where $\mathit{af}(x_{1},\ldots,x_{n})=\big{(}\mathit{af}_{v_{1}}(x_{1},\ldots,x_{n}), \ldots,\mathit{af}_{v_{n}}(x_{1},\ldots,x_{n})\big{)}$.

Recall the example program from Section 4.1:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172012315.png)
Its CFG looks as follows, with nodes $\{v_{1},\ldots,v_{8}\}$:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172012787.png)

**Exercise 5.6**: Generate the equation system for this example program. Then solve the equations using the fixed-point algorithm from Section 4.4.

(Notice that the least upper bound operation is exactly what we need to model the merging of information at $v_{8}$!)

**Exercise 5.7**: Write a small TIP program where the sign analysis leads to an equation system with mutually recursive constraints. Then explain step-by-step how the fixed-point algorithm from Section 4.4 computes the solution.

We lose some information in the above analysis, since for example the expressions $(2>0)==1$ and $x-x$ are analyzed as $\top$, which seems unnecessarily coarse. (These are examples where the least fixed point of the analysis equation system is not identical to the semantically best possible answer.) Also, + divided by + results in $\top$ rather than + since e.g. $1 / 2$ is rounded down to zero. To handle some of these situations more precisely, we could enrich the sign lattice with element 1 (the constant 1 ), $0+$ (positive or zero), and $\theta-$ (negative or zero) to keep track of more precise abstract values:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172015440.png)

and consequently describe the abstract operators by $8\times 8$ tables.

**Exercise 5.8**: Define the six operators on the extended _Sign_ lattice (shown above) by means of $8\times 8$ tables. Check that they are monotone. Does this new lattice improve precision for the expressions $(2>0)==1, x-x,$ and $1/2$?

**Exercise 5.9**: Show how the _eval_ function could be improved to make the sign analysis able to show that the final value of z cannot be a negative number in the following program:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172016914.png)

**Exercise 5.10**: Explain how to extend the sign analysis to handle TIP programs that use records (see Chapter 2).

One approach, called _field insensitive_ analysis, simply mixes together the different fields of each record. Another approach, _field sensitive_ analysis, instead uses a more elaborate lattice that keeps different abstract values for the different field names.

The results of a sign analysis could in theory be used to eliminate division-by-zero errors by rejecting programs in which denominator expressions have sign $\mathbf{0}$ or $\top$. However, the resulting analysis will probably unfairly reject too many programs to be practical. Other more powerful analysis techniques, such as interval analysis (Section 6.1) and path sensitivity (Chapter 7) would be more useful for detecting such errors.

Notice that in this analysis we use the $\bigsqcup$ operation (in the definition of $JOIN$), but we never use the $\sqcap$ operation. In fact, when implementing analyses with monotone frameworks, it is common that $\sqcap$ is ignored entirely even though it mathematically exists.

## 5.2 Constant Propagation Analysis

An analysis related to sign analysis is constant propagation analysis, where we for every program point want to determine the variables that have a constant value. The analysis is structured just like the sign analysis, except for two modifications. First, the _Sign_ lattice is replaced by $\mathit{flat}(\mathbb{Z})$ where $\mathbb{Z}$ is the set of all integers:[^f3]

[^f3]: For simplicity, we assume that TIP integer values are unbounded.

Second, the abstraction of operators $\mathit{op}\in\{+,-,*,/,>,==\}$ is modified accordingly:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172017259.png)

**Exercise 5.11**: Argue that this definition of $\widehat{\mathit{op}}$ leads to a sound analysis. (An informal argument suffices; we shall see a more formal approach to proving soundness in Section 12.3.)

Using constant propagation analysis, an optimizing compiler could transform the program
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172017245.png)
into
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172017437.png)
which, following a reaching definitions analysis and dead code elimination (see Section 5.7), can be reduced to this shorter and more efficient program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172018764.png)

This kind of optimization was among the first uses of static program analysis [16].

Exercise5.12: Assume that TIP computes with (arbitrary-precision) real numbers instead of integers. Design an analysis that finds out which variables at each program point in a given program only have integer values.

## 5.3 Fixed-Point Algorithms

In summary, dataflow analysis works as follows. For a CFG with nodes $Nodes=\{v_{1},v_{2},\ldots,v_{n}\}$ we work in the complete lattice $L^{n}$ where $L$ is a lattice that models abstract states. Assuming that node $v_{i}$ generates the dataflow equation $[\![v_{i}]\!]=f_{i}([\![v_{1}]\!],\ldots,[\![v_{n}]\!])$, we construct the combined function $f\colon L^{n}\to L^{n}$ by defining $f(x_{1},\ldots,x_{n})=\big{(}f_{1}(x_{1},\ldots,x_{n}),\ldots,f_{n}(x_{1}, \ldots,x_{n})\big{)}$. Applying the fixed-point algorithm, NaiveFixedPointAlgorithm$(f)$ (see page 48), then gives us the desired solution for $[\![v_{1}]\!],\ldots,[\![v_{n}]\!]$.

Exercise 4.30 (page 49) demonstrates why the algorithm is called "naive". In each iteration it applies all the constraint functions, $f_{1},\ldots,f_{4}$, and much of that computation is redundant. For example, $f_{2}$ (see page 47) depends only on $x_{1}$, but the value of $x_{1}$ is unchanged in most iterations.

As a step toward more efficient algorithms, the _round-robin algorithm_ exploits the fact that our lattice has the structure $L^{n}$ and that $f$ is composed from $f_{1},\ldots,f_{n}$:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172018144.png)

(Similar to the naive fixed-point algorithm, it is trivial to avoid computing each $f_{i}(x_{1},\ldots,x_{n})$ twice in every iteration.) Notice that one iteration of the while-loop in this algorithm does not in general give the same result as one iteration of the naive fixed-point algorithm: when computing $f_{i}(x_{1},\ldots,x_{n})$, the values of $x_{1},\ldots,x_{i-1}$ have been updated by the preceding iterations of the inner loop (while the values of $x_{i},\ldots,x_{n}$ come from the previous iteration of the outer loop or are still $\bot$, like in the naive fixed-point algorithm). Nevertheless, the algorithm always terminates and produces the same result as the naive fixed-point algorithm. Each iteration of the while-loop takes the same time as for the naive fixed-point algorithm, but the number of iterations required to reach the fixed point may be lower.

**Exercise 5.13**: Prove that the round-robin algorithm computes the least fixed point of $f$. (Hint: see the proof of the fixed-point theorem, and consider the ascending chain that arises from the sequence of $x_{i}:=f_{i}(x_{1},\ldots,x_{n})$ operations.)

**Exercise 5.14**: Continuing Exercise 4.30, how many iterations are required by the naive fixed-point algorithm and the round-robin algorithm, respectively, to reach the fixed point?

We can do better than round-robin. First, the order of the iterations $i:=1\ldots n$ is clearly irrelevant for the correctness of the algorithm (see your proof from Exercise 5.13). Second, we still apply all constraint functions in each iteration of the repeat-until loop. What matters for correctness is, which should be clear from your solution to Exercise 5.13, that the constraint functions are applied until the fixed point is reached for all of them. This observation leads to the _chaotic-iteration algorithm_[12, 13]:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172019007.png)

This is not a practical algorithm, because its efficiency and termination depend on how $i$ is chosen in each iteration. Additionally, naively computing the loop condition may now be more expensive than executing the loop body. However, _if_ it terminates, the algorithm produces the right result.

**Exercise 5.15**: Prove that the chaotic-iteration algorithm computes the least fixed point of $f$, if it terminates. (Hint: see your solution to Exercise 5.13.)

The algorithm we describe next is a practical variant of chaotic-iteration.

In the general case, every constraint variable $[\![ v_{i} ]\!]$ may depend on all other variables. Most often, however, an actual instance of $f_{i}$ will only read the values of a few other variables, as in the examples from Exercise 4.28 and Exercise 5.6. We represent this information as a map

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172021292.png)

which for each node $v$ tells us the subset of other nodes for which $[\![ v ]\!]$ occurs in a nontrivial manner on the right-hand side of their dataflow equations. That is, $\mathit{dep}(v)$ is the set of nodes whose information may depend on the information of $v$. We also define its inverse: $\mathit{dep}^{-1}(v)=\{w\mid v\in\mathit{dep}(w)\}$.

For the example from Exercise 5.6, we have, in particular, $\mathit{dep}(v_{5})=\{v_{6},v_{7}\}$. This means that whenever $[\![ v_{5} ]\!]$ changes its value during the fixed-point computation, only $f_{6}$ and $f_{7}$ may need to be recomputed.

Armed with this information, we can present a simple _work-list algorithm_:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172023814.png)

The set $W$ is here called the work-list with operations 'add' and'removeNext' for adding and (nondeterministically) removing an item. The work-list initially contains all nodes, so each $f_{i}$ is applied at least once. It is easy to see that the work-list algorithm terminates on any input: In each iteration, we either move up in the $L^{n}$ lattice, or the size of the work-list decreases. As usual, we can only move up in the lattice finitely many times as it has finite height, and the while-loop terminates when the work-list is empty. Correctness follows from observing that each iteration of the algorithm has the same effect on $(x_{1},\ldots,x_{n})$ as one iteration of the chaotic-iteration algorithm for some nondeterministic choice of $i$.

**Exercise 5.16**: Argue that a sound, but probably not very useful choice for the _dep_ map is one that always returns the set of all CFG nodes.

**Exercise 5.17**: As stated above, we can choose $\mathit{dep}(v_{5})=\{v_{6},v_{7}\}$ for the example equation system from Exercise 5.6. Argue that a good strategy for the sign analysis is to define $\mathit{dep}=\mathit{succ}$. (We return to this topic in Section 5.8.)

**Exercise 5.18**: Explain step-by-step how the work-list algorithm computes the solution to the equation system from Exercise 5.6. (Since the'removeNext' operation is nondeterministic, there are many correct answers!)

**Exercise 5.19**: When reasoning about worst-case complexity of analyses that are based on work-list algorithms, it is sometimes useful if one can bound the number of predecessors $|\mathit{pred}(v)|$ or successors $|\mathit{succ}(v)|$ for all nodes $v$.

a. Describe a family of TIP functions where the maximum number of successors $|\mathit{succ}(v)|$ for the nodes $v$ in each function grows linearly in the number of CFG nodes.
b. Now let us modify the CFG construction slightly, such that a dummy "no-op" node is inserted at the merge point after the two branches of each if block. This will increase the number of CFG nodes by at most a constant factor. Argue that we now have $|\mathit{pred}(v)|\leq 2$ and $|\mathit{succ}(v)|\leq 2$ for all nodes $v$.

Assuming that $|\mathit{dep}(v)|$ and $|\mathit{dep}^{-1}(v)|$ are bounded by a constant for all nodes $v$, the worst-case time complexity of the simple work-list algorithm can be expressed as

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172023935.png)

where $n$ is the number of CFG nodes in the program being analyzed, $h$ is the height of the lattice $L$ for abstract states, and $k$ is the worst-case time required to compute a constraint function $f_{i}(x_{1},\ldots,x_{n})$.

**Exercise 5.20**: Prove the above statement about the worst-case time complexity of the simple work-list algorithm. (It is reasonable to assume that the work-list operations 'add' and'removeNext' take constant time.)

**Exercise 5.21**: Another useful observation when reasoning about worst-case complexity of dataflow analyses is that normalizing a program (see Section 2.3) may increase the number of CFG nodes by more than a constant factor, but represented as an AST or as textual source code, the size of the program increases by at most a constant factor. Explain why this claim is correct.

**Exercise 5.22**: Estimate the worst-case time complexity of the sign analysis with the simple work-list algorithm, using the formula above. (As this formula applies to _any_ dataflow analysis implemented with the simple work-list algorithm, the actual worst-case complexity of this specific analysis may be asymptotically better!)

Further algorithmic improvements are possible. It may be beneficial to handle in separate turns the strongly connected components of the graph induced by the _dep_ map, and the worklist set could be changed into a priority queue allowing us to exploit domain-specific knowledge about a particular dataflow problem. Also, for some analyses, the dependence information can be made more precise by allowing _dep_ to consider the current value of $(x_{1},\ldots,x_{n})$ in addition to the node $v$.

## 5.4 Live Variables Analysis

A variable is _live_ at a program point if there exists an execution where its value is read later in the execution without it being written to in between. Clearly undecidable, this property can be approximated by a static analysis called live variables analysis (or liveness analysis). The typical use of live variables analysis is optimization: there is no need to store the value of a variable that is not live. For this reason, we want the analysis to be conservative in the direction where the answer "not live" can be trusted and "live" is the safe but useless answer.

We use a powerset lattice where the elements are the variables occurring in the given program. This is an example of a _parameterized_ lattice, that is, one that depends on the specific program being analyzed. For the example program

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172024146.png)

the lattice modeling abstract states is thus:[^f4]

[^f4]: A word of caution: For historical reasons, some textbooks and research papers, e.g. [10, 11], describe dataflow analyses using the lattices “upside down”. This makes no difference whatsoever to the analysis results (because of the lattice dualities discussed in Chapter 4), but it can be confusing.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172025151.png)

The corresponding CFG looks as follows:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172025349.png)
For every CFG node v we introduce a constraint variable $[\![ v ]\!]$ denoting the subset of program variables that are live at the program point before that node. The analysis will be conservative, since the computed set may be too large. We use the auxiliary definition

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172026118.png)
Unlike the $\mathit{JOIN}$ function from sign analysis, this one combines abstract states from the successors instead of the predecessors. We have defined the order relation as $\sqsubseteq$$=$$\subseteq$, so $\sqcup=$$\cup$.

As in sign analysis, the most interesting constraint rule is the one for assignments:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172027473.png)

This rule models the fact that the set of live variables before the assignment is the same as the set after the assignment, except for the variable being written to and the variables that are needed to evaluate the right-hand-side expression.

**Exercise 5.23**: Explain why the constraint rule for assignments, as defined above, is sound.

Branch conditions and output statements are modelled as follows:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172027716.png)

where $\mathit{vars}(E)$ denotes the set of variables occurring in $E$. For variable declarations and exit nodes:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172028865.png)

For all other nodes:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172028389.png)

**Exercise 5.24**: Argue that the right-hand sides of the constraints define monotone functions.

The example program yields these constraints:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172028502.png)

whose least solution is:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172029989.png)
From this information a clever compiler could deduce that $\mathrm{y}$ and $\mathrm{z}$ are never live at the same time, and that the value written in the assignment $\mathrm{z}=\mathrm{z}-1$ is never read. Thus, the program may safely be optimized into the following one, which saves the cost of one assignment and could result in better register allocation:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172030485.png)

**Exercise 5.25**: Consider the following program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172030839.png)
Show for each program point the set of live variables, as computed by our live variables analysis. (Do not forget the entry and exit points.)

**Exercise 5.26**: An analysis is distributive if all its constraint functions are distributive according to the definition from Exercise 4.20. Show that live variables analysis is distributive.

**Exercise 5.27**: As Exercise 5.25 demonstrates, live variables analysis is not ideal for locating code that can safely be removed, if building an optimizing compiler. Let us define that a variable is _useless_ at a given program point if it is dead (i.e. not live) or its value is only used to compute values of useless variables. A variable is _strongly live_ if it is not useless.

* Show how the live variables analysis can be modified to compute strongly live variables.
* Show for each program point in the program from Exercise 5.25 the set of strongly live variables, as computed by your new analysis.

We can estimate the worst-case time complexity of the live variables analysis, with for example the naive fixed-point algorithm from Section 4.4. We first observe that if the program has $n$ CFG nodes and $b$ variables, then the lattice $\mathcal{P}(\mathit{Vars})^{n}$ has height $b\cdot n$, which bounds the number of iterations we can perform. Each lattice element can be represented as a bitvector of length $b\cdot n$. Using the observation from Exercise 5.19 we can ensure that $|\mathit{succ}(v)|\leq 2$ for any node $v$. For each iteration we therefore have to perform $\mathcal{O}(n)$ intersection, difference, or equality operations on sets of size $b$, which can be done in time $\mathcal{O}(b\cdot n)$. Thus, we reach a time complexity of $\mathcal{O}(b^{2}\cdot n^{2})$.

**Exercise 5.28**: Can you obtain an asymptotically better bound on the worst-case time complexity of live variables analysis with the naive fixed-point algorithm, if exploiting properties of the structures of TIP CFGs and the analysis constraints?

**Exercise 5.29**: Recall from Section 5.3 that the work-list algorithm relies on a function $\mathit{dep}(v)$ for avoiding recomputation of constraint functions that are guaranteed not to change outputs. What would be a good strategy for defining $\mathit{dep}(v)$ in general for live variables analysis of any given program?

**Exercise 5.30**: Estimate the worst-case time complexity of the live variables analysis with the simple work-list algorithm, by using the formula from page 5.1.

## 5.5 Available Expressions Analysis

A nontrivial expression in a program is _available_ at a program point if its current value has already been computed earlier in the execution. Such information is useful for program optimization. The set of available expressions for all program points can be approximated using a dataflow analysis. The lattice we use has aselements all expressions occurring in the program. To be useful for program optimization purposes, an expression may be included at a given program point only if it is _definitely_ available no matter how the computation arrived at that program point, so we choose the lattice to be ordered by _reverse_ subset inclusion.

For the program

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172031968.png)

we have four different nontrivial expressions, so our lattice for abstract states is

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172031927.png)

which looks like this:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172031034.png)

The top element of our lattice is $\emptyset$, which corresponds to the trivial information that no expressions are known to be available. The CFG for the above program looks as follows:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172031568.png)

As usual in dataflow analysis, for each CFG node $v$ we introduce a constraint variable $[v]$ ranging over $States$. Our intention is that it should contain the subset of expressions that are guaranteed always to be available at the program point after that node. For example, the expression a+b is available at the condition in the loop, but it is not available at the final assignment in the loop. Our analysis will be conservative in the sense that the computed sets may be too small but never too large.

Next we define the dataflow constraints. The intuition is that an expression is available at a node $v$ if it is available from all incoming edges or is computed by $v$, unless its value is destroyed by an assignment statement.

The $JOIN$ function uses $\cap$ (because the lattice order is now $\supseteq$) and _pred_ (because availability of expressions depends on information from the past):

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172032277.png)
Assignments are modeled as follows:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172032258.png)

Here, the function $\downarrow\!X$ removes all expressions that contain the variable $X$, and $\mathit{exps}$ collects all nontrivial expressions:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172032928.png)

No expressions are available at entry nodes:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172032000.png)

Branch conditions and output statements accumulate more available expressions:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172033532.png)

For all other kinds of nodes, the collected sets of expressions are simply propagated from the predecessors:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172033258.png)

Again, the right-hand sides of all constraints are monotone functions.

**Exercise5.31**: Explain informally why the constraints are monotone and the analysis is sound.

For the example program, we generate the following constraints:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172033012.png)

Using one of our fixed-point algorithms, we obtain the minimal solution:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172034958.png)

The expressions available at the program point _before_ a node $v$ can be computed from this solution as $JOIN(v)$. In particular, the solution confirms our previous observations about a+b. With this knowledge, an optimizing compiler could systematically transform the program into a (slightly) more efficient version:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172034215.png)
**Exercise 5.32**: Estimate the worst-case time complexity of available expres- sions analysis, assuming that the naive fixed-point algorithm is used.

## 5.6 Very Busy Expressions Analysis

An expression is very busy if it will definitely be evaluated again before its value changes. To approximate this property, we can use the same lattice and auxiliary functions as for available expressions analysis. For every CFG node v the variable $[\![ v ]\!]$ denotes the set of expressions that at the program point before the node definitely are busy.

An expression is very busy if it is evaluated in the current node or will be evaluated in all future executions unless an assignment changes its value. For this reason, the JOIN is defined by
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172046550.png)
and assignments are modeled using the following constraint rule:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172047160.png)
No expressions are very busy at exit nodes:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172047283.png)
The rules for the remaining nodes, include branch conditions and output statements, are the same as for available expressions analysis.

On the example program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172047301.png)
the analysis reveals that $a * b$ is very busy inside the loop. The compiler can perform code hoisting and move the computation to the earliest program point where it is very busy. This would transform the program into this more efficient version:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172048548.png)

## 5.7 Reaching Definitions Analysis

The _reaching definitions_ for a given program point are those assignments that may have defined the current values of variables. For this analysis we need a powerset lattice of all assignments (represented as CFG nodes) occurring in the program. For the example program from before:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172048569.png)

the lattice modeling abstract states becomes:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172048986.png)

For every CFG node $v$ the variable $[v]$ denotes the set of assignments that may define values of variables at the program point after the node. We define
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172048430.png)
For assignments the constraint is:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172049128.png)

where this time the $\downarrow X$ function removes all assignments to the variable $X$. For all other nodes we define:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172049623.png)

This analysis can be used to construct a _def-use graph_, which is like a CFG except that edges go from definitions (i.e. assignments) to possible uses. Here is the def-use graph for the example program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172049844.png)

The def-use graph is a further abstraction of the program and is the basis of widely used optimizations such as _dead code elimination_ and _code motion_.

**Exercise 5.33**: Show that the def-use graph is always a subgraph of the transitive closure of the CFG.

## 5.8 Forward, Backward, May, and Must

As illustrated in the previous sections, a dataflow analysis is specified by providing the lattice and the constraint rules. Some patterns are emerging from the examples, which makes it possible to classify dataflow analyses in various ways.

A _forward_ analysis is one that for each program point computes information about the _past_ behavior. Examples of this are sign analysis and available expressions analysis. They can be characterized by the right-hand sides of constraints only depending on _predecessors_ of the CFG node. Thus, the analysis essentially starts at the _entry_ node and propagates information forward in the CFG. For such analyses, the $JOIN$ function is defined using _pred_, and _dep_ (if using the work-list algorithm) can be defined by _succ_.

A _backward_ analysis is one that for each program point computes information about the _future_ behavior. Examples of this are live variables analysis and very busy expressions analysis. They can be characterized by the right-hand sides of constraints only depending on _successors_ of the CFG node. Thus, the analysis starts at the _exit_ node and moves backward in the CFG. For such analyses, the _JOIN_ function is defined using _succ_, and _dep_ can be defined by _pred_.

The distinction between forward and backward applies to any flow-sensitive analysis. For analyses that are based on a powerset lattice, we can also distinguish between _may_ and _must_ analysis.

A _may_ analysis is one that describes information that may possibly be true and, thus, computes an _over_-approximation. Examples of this are live variables analysis and reaching definitions analysis. They can be characterized by the lattice order being $\subseteq$ and constraint functions that use the $\cup$ operator to combine information.

Conversely, a _must_ analysis is one that describes information that must definitely be true and, thus, computes an _under_-approximation. Examples of this are available expressions analysis and very busy expressions analysis. They can be characterized by the use of $\supseteq$ as lattice order and constraint functions that use $\cap$ to combine information.

Thus, our four examples that are based on powerset lattices show every possible combination, as illustrated by this diagram:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172049304.png)
These classifications are mostly botanical, but awareness of them may provide inspiration for constructing new analyses.

**Exercise 5.34**: Which among the following analyses are distributive, if any?

1. Available expressions analysis.
2. Very busy expressions analysis.
3. Reaching definitions analysis.
4. Sign analysis.
5. Constant propagation analysis.

**Exercise 5.35**: Let us design a _flow-sensitive type analysis_ for TIP. (This exercise can be seen as an alternative to the approach in Exercise 3.22.) In the simple version of TIP we focus on in this chapter, we only have integer values at runtime, but for the analysis we can treat the results of the comparison operators > and == as a separate type: boolean. The results of the arithmetic operators +, -, *, / can similarly be treated as type integer. As lattice for abstract states we choose

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172050901.png)

such that the analysis can keep track of the possible types for every variable.

* Specify constraint rules for the analysis.
* After analyzing a given program, how can we check using the computed abstract states whether the branch conditions in if and while statements are guaranteed to be booleans? Similarly, how can we check that the arguments to the arithmetic operators +, -, *, / are guaranteed to be integers? As an example, for the following program two warnings should be emitted:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172050078.png)

**Exercise 5.36**: Assume we want to build an optimizing compiler for TIP (without pointers, function calls, and records). As part of this, we want to safely approximate the possible values for each variable to be able to pick appropriate runtime representations: bool (can represent only the two integer values 0 and 1), byte (8 bit signed integers), char (16 bit unsigned integers), int (32 bit signed integers), or bignt (any integer). Naturally, we do not want to waste space, so we prefer, for example, bit to int if we can guarantee that the value of the variable can only be 0 or 1.

As an extra feature, we introduce a cast operation in TIP: an expression of the form $(T)E$ where $T$ is one of the five types and $E$ is an expression. At runtime, a cast expression evaluates to the same value as $E$, except that it aborts program execution if the value does not fit into $T$.

1. Define a suitable lattice for describing abstract states.
2. Specify the constraint rules for your analysis.
3. Write a small but nontrivial TIP program that gives rise to several different types, and argue briefly what result your analysis will produce for that program.

## 5.9 Initialized Variables Analysis

Let us try to define an analysis that ensures that variables are initialized (i.e. written to) before they are read. (A similar analysis is performed by Java compilers to check that every local variable has a definitely assigned value when any access of its value occurs.) This can be achieved by computing for every program point the set of variables that are guaranteed to be initialized. We need definite information, which implies a must analysis. Consequently, we choose as abstract state lattice the powerset of variables occurring in the given program, ordered by the superset relation. Initialization is a property of the past, so we need a forward analysis. This means that our constraints are phrased in terms of predecessors and intersections. On this basis, the constraint rules more or less give themselves.

**Exercise 5.37**: What is the $JOIN$ function for initialized variables analysis?

**Exercise 5.38**: Specify the constraint rule for assignments.

No other statements than assignments affect which variables are initialized, so the constraint rule for all other kinds of nodes is the same as, for example, in sign analysis (see page 5.1).

Using the results from initialized variables analysis, a programming errordetection tool could now check for every use of a variable that it is contained in the computed set of initialized variables, and emit a warning otherwise. A warning would be emitted for this trivial example program:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172051436.png)

**Exercise 5.39**: Write a TIP program where such an error detection tool would emit a _spurious warning_. That is, in your program there are no reads from uninitialized variables in any execution but the initialized variables analysis is too imprecise to show it.

**Exercise 5.40**: An alternative way to formulate initialized variables analysis would be to use the following map lattice instead of the powerset lattice:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172051033.png)

where $\mathit{Init}$ is a lattice with two elements ${Initialized, NotIninitialized}$.

1. How should we order the two elements? That is, which one is $\top$ and which one is $\bot$?
2. How should the constraint rule for assignments be modified to fit with this alternative lattice?

## 5.10 Transfer Functions

Observe that in all the analyses presented in this chapter, all constraint functions are of the form

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172051713.png)

for some function $t_{v}\colon L\to L$ where $L$ is the lattice modeling abstract states and $\mathit{JOIN}(v)=\bigsqcup_{w\in\mathit{dep}^{-1}(v)} [\![ w ]\!]$. The function $t_{v}$ is called the _transfer function_ for the CFG node $v$ and specifies how the analysis models the statement at $v$ as an abstract state transformer. For a forward analysis, which is the most common kind of dataflow analysis, the input to the transfer function represents the abstract state at the program point immediately before the statement, and its output represents the abstract state at the program point immediately after the statement (and conversely for a backward analysis). When specifying constraints for a dataflow analyses, it thus suffices to provide the transfer functions for all CFG nodes. As an example, in sign analysis where $L=\mathit{Vars}\to\mathit{Sign}$, the transfer function for assignment nodes $X=E$ is:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172052996.png)

In the simple work-list algorithm, $JOIN(v)=\bigsqcup_{w\in dep^{-1}(v)}[\![w]\!]$ is computed in each iteration of the while-loop. However, often $[\![w]\!]$ has not changed since last time $v$ was processed, so much of that computation may be redundant. (When we introduce inter-procedural analysis in Chapter 8, we shall see that $dep^{-1}(v)$ may become large.) We now present another work-list algorithm based on transfer functions that avoids some of that redundancy. With this algorithm, for a forward analysis each variable $x_{i}$ denotes the abstract state for the program point _before_ the corresponding CFG node $v_{i}$, in contrast to the other fixed-point solvers we have seen previously where $x_{i}$ denotes the abstract state for the program point _after_$v_{i}$ (and conversely for a backward analysis).

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311172052763.png)

Compared to the simple work-list algorithm, this variant typically avoids many redundant least-upper-bound computations. In each iteration of the while-loop, the transfer function of the current node $v_{i}$ is applied, and the resulting abstract state is propagated (hence the name of the algorithm) to all dependencies. Those that change are added to the work-list. We thereby have $t_{v}([v])\sqsubseteq[\![w]\!]$ for all nodes $v,w$ where $w\in succ(v)$.

**Exercise5.41**: Prove thatPropagationWorkListAlgorithm computes the same solution as the other fixed-point solvers. (Hint: recall the discussion from page 49 about solving systems of inequations.)
