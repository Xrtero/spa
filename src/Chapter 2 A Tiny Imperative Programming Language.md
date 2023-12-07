# Chapter 2 A Tiny Imperative Programming Language

We use a tiny imperative programming language, called _TIP_, throughout the following chapters. It is designed to have a minimal syntax and yet to contain all the constructions that make static analyses interesting and challenging. Different language features are relevant for the different static analysis concepts, so in each chapter we focus on a suitable fragment of the language.

## 2.1 The Syntax of TIP

In this section we present the formal syntax of the TIP language, expressed as a context-free grammar. TIP programs interact with the world simply by reading input from a stream of integers (for example obtained from the user's keyboard) and writing output as another stream of integers (to the user's screen). The language lacks many features known from commonly used programming languages, for example, global variables, nested functions, objects, and type annotations. We will consider some of those features in exercises in later chapters.

### Basic Expressions

The basic expressions all denote integer values:

Expressions Exp include integer literals Int and variables (identifiers) I d. The input expression reads an integer from the input stream. The comparison operators yield 0 for false and 1 for true. Function calls, pointer operations, and record operations will be added later.

### Statements

The simple statements $Stm$ are familiar:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162302470.png)
We use the notation $[\ldots]^{?}$ to indicate optional parts. In the conditions we interpret 0 as false and all other values as true. The output statement writes an integer value to the output stream.

### Functions

A function declaration $F$ contains a function name, a list of parameters, local variable declarations, a body statement, and a return expression:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162302138.png)
Function names and parameters are identifiers, like variables. The var block declares a collection of uninitialized local variables. Function calls are an extra kind of expression:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162303767.png)
We sometimes treat var blocks and return instructions as statements.
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162303145.png)
Unlike simple function calls, the function being called is now an expression that evaluates to a function value. Function values allow us to illustrate the main challenges that arise with methods in object-oriented languages and with higher-order functions in functional languages.
The following example program contains three functions:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162304070.png)
In the `main` function, the inc function is passed as argument to the `twice` func-tion, which calls the given function twice.

### Pointer

To be able to build data structures and dynamically allocate memory, we introduce pointers:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162305930.png)
The first expression allocates a new cell in the heap initialized with the value of the given expression and results in a pointer to the cell. The second expression creates a pointer to a program variable, and the third expression dereferences a pointer value (this is also called a load operation). In order to assign values through pointers we allow another form of assignment (called a store operation):
![](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162305343.png)
In such an assignment, if the expression on the left-hand-side evaluates to a pointer to a cell, then the value of the right-hand-side expression is stored in that cell. Pointers and integers are distinct values, and pointer arithmetic is not possible.
The following example illustrates the various pointer operations:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162306515.png)
The first line allocates a cell initially holding the value null, after the second line y points to the variable x, the third line assigns the value 42 to the cell allocated in the first line (thereby overwriting the null value), and the fourth line reads the new value of that cell via two pointer dereferences.

### Records

A record is a collection of fields, each having a name and a value. The syntax for creating records and for reading field values looks as follows:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162307739.png)
Here is an example:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162307407.png)
The first line creates a record with two fields: one with name f and value 1 , and one with name g and value 2 . The second line reads the value of the f field.

To update the values of record fields we allow two other forms of assignment, for writing directly to a record held by variable or indirectly via a pointer, respectively:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162307989.png)
Consider this example:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162307727.png)
Here, $\mathrm{x}$ holds a record, $\mathrm{y}$ holds a pointer to the same record, and the two last assignments update the values of the fields f and g of the record.

Records are passed by value, so, for example, if $\mathrm{x}$ holds a record then a simple assignment $z=x$; copies the record to z. For simplicity, the values of record fields cannot themselves be records (but they can be, for example, pointers to records).

### Programs

A complete program is just a collection of functions:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162308819.png)
(We sometimes also refer to indivial functions or statements as programs.) For a complete program, the function named main is the one that initiates execution. Its arguments are supplied in sequence from the beginning of the input stream, and the value that it returns is appended to the output stream.

We often use meta-variables $I \in I n t, X \in I d, E \in \operatorname{Exp}, S \in \operatorname{Stm}, F \in Fun, P \in Prog$, sometimes with subscripts, ranging over the different syntactic categories.

To keep the presentation short, we deliberately have not specified all details of the TIP language, neither the syntax nor the semantics.

**Exercise 2.1**: Identify some of the under-specified parts of the TIP language, and propose meaningful choices to make it more well-defined.

In Chapter 12 we formally define semantics for a part of TIP.

## 2.2 Example Programs

The following TIP programs all compute the factorial of a given integer. The first one is iterative:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162310273.png)
The second program is recursive:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162310140.png)

The third program is unnecessarily complicated:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311171551926.png)

More example programs can be found in the Scala implementation of TIP.

## 2.3 Normalization

A rich and flexible syntax is useful when writing programs, but when describing and implementing static analyses, it is often convenient to work with a syntactically simpler language. For this reason we sometimes normalize programs by transforming them into equivalent but syntactically simpler ones. A particularly useful normalization is to flatten nested pointer expressions, such that pointer dereferences are always of the form *Id rather than the more general*Exp, and similarly, function calls are always of the form $Id(I d, \ldots, I d)$ rather than $\operatorname{Exp}(\operatorname{Exp}, \ldots, \operatorname{Exp})$. It may also be useful to flatten arithmetic expressions, arguments to direct calls, branch conditions, and return expressions.

As an example,
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162327102.png)
can be normalized to
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162327939.png)
where t1 and t2 are fresh variables, whereby each statement performs only one operation.

**Exercise2.2**: Argue that any TIP program can be normalized so that all expressions, with the exception of right-hand side expressions of assignments, are variables. (This is sometimes called _A-normal form_[13].)

**Exercise 2.3**:Show how the following statement can be normalized: ``x=(**f)(g()+h());``

Exercise 2.4: Assume we want to normalize pointer operations such that load operations are restricted to statements of the form $I d={ }^{*} I d$; and store operations are restricted to statements of the form ${ }^{*} I d=I d$; . Explain how the statement ${ }^{* *} \mathrm{x}=* * \mathrm{y}$; can be normalized to this restricted syntax.

TIP uses lexical scoping, however, we make the notationally simplifying assumption that all declared variable and function names are unique in a program, i.e. that no identifiers is declared more than once.

**Exercise 2.5**: Argue that any TIP program can be normalized so that all declared identifiers are unique.

For real programming languages, we often use variations of the intermediate representations of compilers or virtual machines as foundation for implementing analyzers, rather than using the high-level source code.

## 2.4 Abstract Syntax Trees

Abstract syntax trees (ASTs) as known from compiler construction provide a representation of programs that is suitable for _flow-insensitive_ analyses, for example, type analysis (Chapter 3), control flow analysis (Chapter 10), and pointer analysis (Chapter 11). Such analyses ignore the execution order of statements in a function or block, which makes ASTs a convenient representation. As an example, the AST for the iterate program can be illustrated as follows.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162329403.png)

With this representation, it is easy to extract the set of statements and their structure for each function in the program.

## 2.5 Control Flow Graphs

For _flow-sensitive_ analysis, in particular dataflow analysis (Chapter 5), where statement order matters it is more convenient to view the program as a _control flow graph_, which is a different representation of the program code. This idea goes back to the very first program analyzers in optimizing compilers [1].

We first consider the subset of the TIP language consisting of a single function body without pointers. Control flow graphs for programs comprising multiple functions are treated in Chapters 8 and 10.

A control flow graph (CFG) is a directed graph, in which _nodes_ correspond to statements and _edges_ represent possible flow of control. For convenience, and without loss of generality, we can assume a CFG to always have a single point of entry, denoted _entry_, and a single point of exit, denoted _exit_. We may think of these as no-op statements.

If $v$ is a node in a CFG then $\mathit{pred}(v)$ denotes the set of predecessor nodes and $\mathit{succ}(v)$ the set of successor nodes.

For programs that are fully normalized (cf. Section 2.3), each node corresponds to only one operation.

For now, we only consider simple statements, for which CFGs may be constructed in an inductive manner. The CFGs for assignments, output, return statements, and declarations look as follows:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162329119.png)

For the sequence $S_{1}$$S_{2}$, we eliminate the exit node of $S_{1}$ and the entry node of $S_{2}$ and glue the statements together:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162329474.png)

Similarly, the other control structures are modeled by inductive graph constructions (sometimes with branch edges labeled with true and false):
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162329305.png)
Using this systematic approach, the iterative factorial function results in the following CFG:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162330172.png)

**Exercise 2.6**: Draw the AST and the CFG for the **rec** program from Section 2.2.

**Exercise 2.7**: If TIP were to be extended with a do-while construct (as in `do { x=x-1; } while(x>0)`), what would the corresponding control flow graphs look like?

**Exercise 2.8**: If TIP were to be extended with a do-while construct (as in `do { x=x-1; } while(x>0)`), what would the corresponding control flow graphs look like?
