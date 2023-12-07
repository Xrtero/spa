# Chapter 3 Type Analysis

The TIP programming language does not have explicit type declarations, but of course the various operations are intended to be applied only to certain kinds of values. Specifically, the following restrictions seem reasonable:

* arithmetic operations and comparisons apply only to integers;
* conditions in control structures must be integers;
* only integers can be input and output of the main function;
* only functions can be called, and with correct number of arguments;
* the unary \* operator only applies to pointers (or null);
* field accesses are only performed on records, not on other types of values; and
* the fields being accessed are guaranteed to be present in the records.

We assume that their violation results in runtime errors. Thus, for a given program we would like to know that these requirements hold during execution. Since this is a nontrivial question, we immediately know (Section 1.3) that it is undecidable.

We resort to a conservative approximation: _typability_. A program is typable if it satisfies a collection of type constraints that is systematically derived, typically from the program AST. The type constraints are constructed in such a way that the above requirements are guaranteed to hold during execution, but the converse is not true. Thus, our type analysis will be conservative and reject some programs that in fact will not violate any requirements during execution.

In most mainstream programming languages with static type checking, the programmer must provide type annotations for all declared variables and functions. Type annotations serve as useful documentation, and they also make iteasier to design and implement type systems. TIP does not have type annotations, so our type analysis must infer all the types, based on how the variables and functions are being used in the program.

**Exercise 3.1**: Type checking also in mainstream languages like Java may reject programs that cannot encounter runtime type errors. Give an example of such a program. To make the exercise nontrivial, every instruction in your program should be reachable by some input.

**Exercise 3.2**: Even popular programming languages may have static type systems that are unsound. Inform yourself about Java's covariant typing of arrays. Construct an example Java program that passes all of javac's type checks but generates a runtime error due to this covariant typing. (Note that, because you do receive runtime errors, Java's _dynamic_ type system _is_ sound, which is important to avert malicious attacks.)

The type analysis presented in this chapter is a variant of the Damas-Hindley-Milner technique [12, 13, 14], which forms the basis of the type systems of many programming languages, including ML, OCaml, and Haskell. Our constraint-based approach is inspired by Wand [14]. To simplify the presentation, we postpone treatment of records until Section 3.4, and we discuss other possible extensions in Section 3.5.

The initial values of local variables are undefined in TIP programs, however, for this type analysis we assume that all the variables are initialized before they are used. In other words, this analysis is sound only for programs that never read from uninitialized variables. (A separate analysis that is designed specifically to check whether that property is satisfied is presented in Section 5.9.)

## 3.1 Types

We first define a language of _types_ that will describe possible values:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171552198.png)

These type terms describe respectively integers, pointers, and functions. As an example, we can assign the type (int)$\rightarrow$int to the iterate function from Section 2.2 and the type $\mathsf{int}$int to the first parameter p of the foo function. Each kind of term is characterized by a _term constructor_ with some arity. For example, $\mathsf{1}$ is a term constructor with arity $1$ as it has one sub-term, and the arity of a function type constructor (...)$\rightarrow\dots$ is the number of function parameters plus one for the return type.

The grammar would normally generate finite types, but for recursive functions and data structures we need _regular_ types. Those are defined as regular trees defined over the above constructors. (A possibly infinite tree is _regular_ if it contains only finitely many different subtrees.)

For example, we need infinite types to describe the type of the foo function from Section 2.2, since the second parameter x may refer to the foo function itself:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171553320.png)
To express such recursive types concisely, we add the $\mu$ operator and type variables to the language of types:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171553581.png)

We use meta-variables $\tau\in\mbox{\it Type}$ and $\alpha\in\mbox{\it TypeVar}$, often with subscripts, ranging over types and type variables. A type of the form $\mu\alpha.\tau$ is considered identical to the type $\tau[\mu\alpha.\tau/\alpha]$.[^f1] With this extra notation, the type of the foo function can be expressed like this:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171553932.png)

[^f1]: Think of a term $\mu\alpha.\tau$ as a quantifier that binds the type variable $\alpha$ in the sub-term $\tau$. An occurrence of $\alpha$ in a term $\tau$ is _free_ if it is not bound by an enclosing $\mu\alpha$. The notation $\tau_{1}[\tau_{2}/\alpha]$ denotes a copy of $\tau_{1}$ where all free occurrences of $\alpha$ have been substituted by $\tau_{2}$.

**Exercise 3.3**: Explain how regular types can be represented by finite automata so that two types are equal if their automata accept the same language. Show an automaton that represents the type $\mu \mathrm{t} .(\uparrow int, \mathrm{t}) \rightarrow int.$.

We allow free type variables (i.e., type variables that are not bound by an enclosing $\mu$). Such type variables are implicitly universally quantified, meaning that they represent any type. Consider for example the following function:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171554786.png)

It has type $(\mathrm{t}, \uparrow \mathrm{t}) \rightarrow \mathrm{int}$ is a free type variable meaning that it can be any type, which corresponds to the polymorphic behavior of the function. Note that such type variables are not necessarily entirely unconstrained: the type of a may be anything, but it must match the type of whatever b points to. The more restricted type $(int, \uparrow int) \rightarrow int$ is also a valid type for the store function, but we are usually interested in the most general solutions.

**Exercise 3.4**: What are the types of rec, f, and n in the recursive factorial program from Section 2.2?

**Exercise 3.5**: Write a TIP program that contains a function with type

Type variables are not only useful for expressing recursive types; we also use them in the following section to express systems of type constraints.

## 3.2 Type Constraints

For a given program we generate a constraint system and define the program to be typable when the constraints are solvable. In our case we only need to consider equality constraints over regular type terms with variables. This class of constraints can be efficiently solved using a unification algorithm.

For each local variable, function parameter, and function name $X$ we introduce a type variable $[\![X]\!]$, and for each occurrence of a non-identifier expression $E$ a type variable $[\![E]\!]$. Here, $E$ refers to a concrete node in the abstract syntax tree - not to the syntax it corresponds to. This makes our notation slightly ambiguous but simpler than a pedantically correct description. (To avoid ambiguity, one could, for example, use the notation $[\![E]\!]_{v}$ where $v$ is a unique ID of the syntax tree node.) Assuming that all declared identifiers are unique (see Exercise 2.5), there is no need to use different type variables for different occurrences of the same identifier.

The constraints are systematically defined for each expression, statement, and function in the given program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171554479.png)
The notation $'op'$ here represents any of the binary operators, except == which has its own rule. In the rule for null, $\alpha$ denotes a fresh type variable. (The purpose of this analysis is not to detect potential null pointer errors, so this simple model of null suffices.) Note that program variables and var blocks do not yield any constraints and that parenthesized expression are not present in the abstract syntax.

For the program

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171555995.png)
we obtain the following constraints:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171556761.png)
Most of the constraint rules are straightforward. For example, for any syntactic occurrence of $E_{1}$=$E_{2}$ in the program being analyzed, the two sub-expressions $E_{1}$ and $E_{2}$ must have the same type, and the result is always of type integer.

**Exercise3.6**: Explain each of the above type constraint rules, most importantly those involving functions and pointers.

For a complete program, we add constraints to ensure that the types of the parameters and the return value of the main function are int:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171556220.png)
In this way, a given program (or fragment of a program) gives rise to a collection of equality constraints on type terms with variables, and the collection of constraints can be built by a simple traversal of the AST of the program being analyzed. The order by which the AST is traversed is irrelevant.

All term constructors furthermore satisfy the general term equality axiom:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171556827.png)

where $c$ and $c^{\prime}$ are term constructors and each $\tau_{i}$ and $\tau_{i}^{\prime}$ is a sub-term. In the previous example two of the constraints are $[\![y]\!] = \uparrow [\![x]\!]$  and $[\![y]\!] = \uparrow [\![^\ast y]\!]$, so by the term equality axiom we also have $[\![x]\!] = [\![^\ast y]\!]$.

Furthermore, as one would expect for an equality relation, we have reflexitivity, symmetry, and transitivity:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171604660.png)
for all terms $\tau_{1}$, $\tau_{2}$, and $\tau_{3}$.

A _solution_ assigns a type to each type variable, such that all equality constraints are satisfied.[^f2] The correctness claim for the type analysis is that the existence of a solution implies that the specified runtime errors cannot occur during execution. A solution for the identifiers in the short program is the following:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171604547.png)

[^f2]: We can define precisely what we mean by “solution” as follows. A _substitution_ is a mapping $\sigma$ from type variables to types. Applying a substitution $\sigma$ to a type $\tau$, denoted $\tau\sigma$, means replacing each free type variable $\alpha$ in $\tau$ by $\sigma(\alpha)$. A _solution_ to a set of type constraints is a substitution $\sigma$ where $\tau_{1}\sigma$ is identical to $\tau_{2}\sigma$ for each of the type constraints $\tau_{1}=\tau_{2}$.

**Exercise 3.7**: Assume y = alloc x in the short function is changed to y = 42. Show that the resulting constraints are unsolvable.

**Exercise 3.8**: Give a reasonable definition of what it means for one solution to be "more general" than another. (See page 21 for an example of two types where one is more general than the other.)

**Exercise 3.9**: This exercise demonstrates the importance of the term equality axiom. First explain what the following TIP code does when it is executed:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171605278.png)
Then generate the type constraints for the code, and apply the unification algorithm (by hand).

**Exercise 3.10**: Extend TIP with _procedures_, which, unlike functions, do not return anything. Show how to extend the language of types and the type constraint rules accordingly.

## 3.3 Solving Constraints with Unification

If solutions exist, then they can be computed in almost linear time using a unification algorithm for regular terms as explained below. Since the constraints may also be extracted in linear time, the whole type analysis is quite efficient.

The unification algorithm we use is based on the familiar union-find data structure (also called a disjoint-set data structure) from 1964 for representing and manipulating equivalence relations [10]. This data structure consists of a directed graph of nodes that each have exactly one edge to its _parent_ node (which may be the node itself in which case it is called a _root_). Two nodes are _equivalent_ if they have a common ancestor, and each root is the _canonical representative_ of its equivalence class. Three operations are provided:[^f3]

[^f3]: We here consider a simple version of union-find without union-by-rank; for a description of the full version with almost-linear worst case time complexity see a textbook on data structures.

* $MakeSet(x)$: adds a new node $x$ that initially is its own parent.
* $Find(x)$: finds the canonical representative of $x$ by traversing the path to the root, performing path compression on the way (meaning that the parent of each node on the traversed path is set to the canonical representative).
* $Union(x,y)$: finds the canonical representatives of $x$ and $y$, and makes one parent of the other unless they are already equivalent.

In pseudo-code:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171606295.png)

The unification algorithm uses union-find by associating a node with each term (including sub-terms) in the constraint system. For each term $\tau$ we initially invoke $MakeSet(\tau)$. Note that each term at this point is either a type variable or a proper type (i.e. integer, pointer, or function); $\mu$ terms are only produced for presenting solutions to constraints, as explained below. For each constraint $\tau_{1}=\tau_{2}$ we invoke $Unify(\tau_{1},\,\tau_{2})$, which unifies the two terms if possible and enforces the general term equality axiom by unifiying sub-terms recursively:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171607891.png)

Unification fails if attempting to unify two terms with different constructors (where function type constructors are considered different if they have different arity).

Note that the $Union(x,\,y)$ operation is asymmetric: it always picks the canonical representative of the resulting equivalence class as the one from the second argument $y$. Also, $Unify$ is carefully constructed such that the second argument to $Union$ can only be a type variable if the first argument is also a type variable. This means that proper types (i.e., terms that are not type variables) take precedence over type variables for becoming canonical representatives, so that it always suffices to consider only the canonical representative instead of all terms in the equivalence class.

Reading the solution after all constraints have been processed is then easy. For each program variable or expression that has an associated type variable, simply invoke $Find$ to find the canonical representative of its equivalence class. If the canonical representative has sub-terms (for example, in the term $\dagger\tau$ we say that $\tau$ is a sub-term), find the solution recursively for each sub-term. The only complication arises if this recursion through the sub-terms leads to an infinite type, in which case we introduce a $\mu$ term accordingly.

**Exercise 3.11**: Argue that the unification algorithm works correctly, in the sense that it finds a solution to the given constraints if one exists. Additionally, argue that if multiple solutions exist, the algorithm finds the uniquely most general one (cf. Exercise 3.8).

(The most general solution, when one exists, for a program expression is also called the _principal type_ of the expression.)

The unification solver only needs to process each constraint once. This means that although we conceptually first generate the constraints and then solve them, in an implementation we might as well interleave the two phases and solve the constraints on-the-fly, as they are being generated.

The complicated factorial program from Section 2.2 generates the following constraints (duplicates omitted):
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171608603.png)

These constraints have a solution, where most variables are assigned int, except these:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171608937.png)

As mentioned in Section 3.1, recursive types are needed for the foo function and the x parameter. Since a solution exists, we conclude that our program is type correct.

**Exercise 3.12**: Check (by hand or using the Scala implementation) that the constraints and the solution shown above are correct for the complicated factorial program.

**Exercise 3.13**: Consider this fragment of the example program shown earlier:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171609501.png)
Explain step-by-step how the unification algorithm finds the solution, including how the union-find data structure looks in each step.

Recursive types are also required when analyzing TIP programs that manipulate data structures. The example program
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171609944.png)
creates these constraints:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171609198.png)
which for $[\![p]\!]$ has the solution $[\![p]\!] = \mu t.\uparrow t$   that can be unfolded to $[\![p]\!] = \uparrow\uparrow\uparrow ....$

**Exercise 3.14**: Show what the union-find data structure looks like for the above example program.

**Exercise 3.15**: Generate and solve the constraints for the `iterate` example program from Section 2.2.

**Exercise 3.16**: Generate and solve the type constraints for this program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171614851.png)
What is the output from running the program?
(Try to find the solutions manually; you can then use the Scala implementation to check that they are correct.)

## 3.4 Record Types

To extend the type analysis to also work for programs that use records, we first extend the language of types with _record types_:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171617328.png)

For example, the record type $\{\texttt{a:int,b:int}\}$ describes records that have two fields, a and b, both with integer values. Record types with different sets of field names are considered as different term constructors.

Our goal is to be able to check conservatively whether the different kinds of errors listed in the beginning of the chapter may appear in the program being analyzed. This means that we need to distinguish records from other kinds of values. Specifically, we want the analysis to check that field accesses are onlyperformed on records, not on other types of values, and that the fields being accessed are present.

As a first attempt, the type constraints for record construction and field lookup can be expressed as follows, inspired by our treatment of pointers and dereferences. (Field write operations are handled in Exercise 3.19.)

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171617819.png)
Intuitively, the constraint rule for field lookup says that the type of E must be a record type that contains a field named X with the same type as E . X. The right-hand-side of this constraint rule is, however, not directly expressible in our language of types. One way to remedy this, without requiring any modifications of our unification algorithm, is to require that every record type contains all record fields that exist in the program, and add a special type, $\diamond$, representing absent fields:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171618962.png)
$Let F=\left\{f_{1}, f_{2}, \ldots, f_{m}\right\}$ be the set of all field names. We then use the following two constraint rules instead of the ones above.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171618155.png)
Each $\alpha_{i}$ denotes a fresh type variable. The constraints of the form $[\![ E . X ]\!]  \neq \diamond$ can easily be checked separately after the unification process has been completed.

**Exercise 3.17**: Explain why it is easier to check the constraints of the form $[\![ E . X ]\!] \neq \diamond$ after instead of during the unification process (i.e., as soon as the other constraints related to field access operations are processed).

As an example, the two statements
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171620653.png)
generate the following constraints, assuming that a, b, and c are the only fields in the program.
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171620405.png)
The unconstrained type variables $x_{1}$ and $x_{2}$ in the solution for $[\![ x ]\!]$ reflect the fact that the fields b and c are irrelevant for the field lookup `x.a`. Similarly, $\diamond$ appears in the solution for $[\![\{b: 42, c: 87\} ]\!]$, because the a field is absent in that record.

**Exercise 3.18**: Generate and solve the type constraints for the following program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171622871.png)
What happens if you change `c.f` to `c.g` in the last line?

**Exercise 3.19**: Specify suitable type constraint rules for both forms of field write statements, $X_{1}$.$X_{2}$=$E$; and (*$E_{1}$).$X$=$E_{2}$;. Then generate and solve the type constraints for the following program:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171623403.png)

**Exercise 3.20**: As mentioned in Section 2.1, the values of record fields in TIP programs cannot themselves be records. How can we extend the type analysis to check whether a given program satisfies this property?

**Exercise 3.21**: Assume we extend the TIP language with array operations. Array values are constructed using a new form of expressions (not to be confused with the syntax for records):
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171623378.png)
and individual elements are read and written as follows:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171623427.png)

For example, the following statements construct an array containing two integers, then overwrites the first one, and finally reads both entries:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171623800.png)
Unlike records, arrays are constructed in the heap and passed by reference, so in the first line, the contents of the array are not copied, and a is like a pointer to the array containing the two integers.

The type system is extended accordingly with an array type constructor:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171624522.png)
As an example, the type `int[][]` denotes arrays of arrays of integers.

Give appropriate type constraints for array operations. Then use the type analysis to check that the following program is typable and infer the type of each program variable:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171624792.png)

**Exercise 3.22**: As mentioned in Chapter 2, TIP does not have booleans as a separate type of values at runtime, but simply represents false as 0 and true as any other integer. Nevertheless, it can be useful to have a static type analysis that rejects expressions like (x > y) _17 and branches like if (x_ 42 - y), since programmers rarely intend to use results of comparisons in integer computations, or use results of integer computations as branch conditions. As a first step, let us extend our language of types with a new type, bool:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171624618.png)

How can we now change the type rules from page 22 such that the resulting type analysis rejects meaningless expressions like those above, but still accepts programs that programmers likely want to write in practice?
(See also Exercise 5.35, which is about a different approach to obtain such type information.)

**Exercise 3.23**: Discuss how TIP could be extended with strings and operations on strings, and how the type analysis could be extended accordingly to check, for example, that the string operations are only applied to strings and not to other types of values.

## 3.5 Limitations of the Type Analysis

The type analysis is of course only approximate, which means that certain programs will be unfairly rejected. A simple example is this:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171625335.png)

This program has no type errors at runtime, but it is rejected by our type checker because the analysis is _flow-insensitive_: the order of execution of the program instructions is abstracted away by the analysis, so intuitively it does not know that x must be an integer at the return expression. In the following chapters we shall see how to perform _flow-sensitive_ analysis that does distinguish between the different program points.

Another limitation, which is even more significant from a practical point of view, is the current treatment of polymorphic types. In fact, polymorphic types are not very useful in their current form. Consider this example program:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171625641.png)

It never causes an error at runtime but is not typable since it among others generates constraints equivalent to
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171626173.png)
which are clearly unsolvable. For this program, we could analyze the f function first, resulting in this polymorphic type:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171626084.png)
When analyzing the main function, at each call to f we could then instantiate the polymorphic type according to the type of the argument: At the first call, the argument has type $\operatorname{\boldsymbol{\uparrow}int}$ so in this case we treat f as having the type $(\operatorname{\boldsymbol{\uparrow}int})\rightarrow\operatorname{\boldsymbol {\uparrow}int}$, and at the second call, the argument has type $\operatorname{\boldsymbol{\uparrow}int}$ so here we treat f as having the type $(\operatorname{\boldsymbol{\uparrow}int})\rightarrow\operatorname{\boldsymbol {\uparrow}int}$. The key property of the program that enables this technique is the observation that the polymorphic function is not recursive. This idea is called _let-polymorphism_ (and this is essentially how Damas-Hindley-Milner-style type analysis actually works in ML and related languages). In Section 8.2 we shall see a closely related program analysis mechanism called _context sensitivity_. The price of the increased precision of let-polymorphism in type analysis is that the worst-case complexity increases from almost-linear to exponential [11, 12].

Even with let-polymorphism, infinitely many other examples will inevitably remain rejected. An example:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171626301.png)

With functions that are both polymorphic and recursive, type analysis becomes undecidable in the general case [13, 11].

**Exercise3.24**: Explain the runtime behavior of the polyrec program, and why it is unfairly rejected by our type analysis, and why let-polymorphism does not help.

Yet another limitation of the type system presented in this chapter is that it ignores many other kinds of runtime errors, such as dereference of null pointers, reading of uninitialized variables, division by zero, and the more subtle _escaping stack cell_ demonstrated by this program:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171627559.png)
The problem in this program is that *p denotes a stack cell that has "escaped" from the baz function. As we shall see in Section 11.7, such problems can instead be handled by other kinds of static analysis.
