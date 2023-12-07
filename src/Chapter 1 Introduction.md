# Chapter 1 Introduction

Static program analysis aims to automatically answer questions about the possible behaviors of programs. In this chapter, we explain why this can be useful and interesting, and we discuss the basic characteristics of analysis tools.

## 1.1 Applications of Static Program Analysis

Static program analysis has been used since the early 1960's in optimizing compilers. More recently, it has proven useful also for bug finding and verification tools, and in IDEs to support program development. In the following, we give some examples of the kinds of questions about program behavior that arise in these different applications.

Analysis for program optimizationOptimizing compilers (including just-in-time compilers in interpreters) need to know many different properties of the program being compiled, in order to generate efficient code. A few examples of such properties are:

* Does the program contain dead code, or more specifically, is function f unreachable from main? If so, the code size can be reduced.
* Is the value of some expression inside a loop the same in every iteration? If so, the expression can be moved outside the loop to avoid redundant computations.
* Does the value of variable x depend on the program input? If not, it could be precomputed at compile time.
* What are the lower and upper bounds of the integer variable x? The answer may guide the choice of runtime representation of the variable.
* Do p and q point to disjoint data structures in memory? That may enable parallel processing.

**Analysis for program correctness** The most successful analysis tools that have been designed to detect errors (or verify absence of errors) target generic correctness properties that apply to most or all programs written in specific programming languages. In unsafe languages like C, such errors sometimes lead to critical security vulnerabilities. In more safe languages like Java, such errors are typically less severe, but they can still cause program crashes. Examples of such properties are:

* Does there exist an input that leads to a null pointer dereference, divisionby-zero, or arithmetic overflow?
* Are all variables initialized before they are read?
* Are arrays always accessed within their bounds?
* Can there be dangling references, i.e., use of pointers to memory that has been freed?
* Does the program terminate on every input? Even in reactive systems such as operating systems, the individual software components, for example device driver routines, are expected to always terminate.

Other correctness properties depend on specifications provided by the programmer for the individual programs (or libraries), for example:

* Are all assertions guaranteed to succeed? Assertions express program specific correctness properties that are supposed to hold in all executions.
* Is function hasNext always called before function next, and is open always called before read? Many libraries have such so-called typestate correctness properties.
* Does the program throw an `ActivityNotFoundException` or a SQLiteException for some input?

With web and mobile software, information flow correctness properties have become extremely important:

* Can input values from untrusted users flow unchecked to file system operations? This would be a violation of integrity.
* Can secret information become publicly observable? Such situations are violations of confidentiality.

The increased use of concurrency (parallel or distributed computing) and eventdriven execution models gives rise to more questions about program behavior:

* Are data races possible? Many errors in multi-threaded programs are caused by two threads using a shared resource without proper synchronization.
* Can the program (or parts of the program) deadlock? This is often a concern for multi-threaded programs that use locks for synchronization.

The most successful Analysis for program developmentModern IDEs perform various kinds of program analysis to support debugging, refactoring, and program understanding. This involves questions, such as:

* Which functions may possibly be called on line 117, or conversely, where can function f possibly be called from? Function inlining and other refactorings rely on such information.
* At which program points could x be assigned its current value? Can the value of variable x affect the value of variable y? Such questions often arise when programmers are trying to understand large codebases and during debugging when investigating why a certain bug appears.
* What types of values can variable x have? This kind of question often arises with programming languages where type annotations are optional or entirely absent, for example OCaml, JavaScript, or Python.

## 1.2 Approximative Answers

Regarding correctness, programmers routinely use testing to gain confidence that their programs work as intended, but as famously stated by Dijkstra [15]: _"Program testing can be used to show the presence of bugs, but never to show their absence."_ Ideally we want guarantees about what our programs may do for all possible inputs, and we want these guarantees to be provided automatically, that is, by programs. A _program analyzer_ is such a program that takes other programs as input and decides whether or not they have a certain property.

Reasoning about the behavior of programs can be extremely difficult, even for small programs. As an example, does the following program code terminate on every integer input n (assuming arbitrary-precision integers)?
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162155641.png)
In 1937, Collatz conjectured that the answer is "yes". As of 2020, the conjecture has been checked for all inputs up to $2^{68}$, but nobody has been able to prove it for all inputs [10].

Even straight-line programs can be difficult to reason about. Does the following program output _true_ for some integer inputs?
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162155025.png)
This was an open problem since 1954 until 2019 when the answer was found after over a million hours of computing [1].

Rice's theorem [10] is a general result from 1953 which informally states that all interesting questions about the input/output behavior of programs (written in Turing-complete programming languages[^f1]) are _undecidable_. This is easily seen for any special case. Assume for example the existence of an analyzer that decides if a variable in a program has a constant value in any execution. In other words, the analyzer is a program $A$ that takes as input a program $T$, one of $T$'s variables $x$, and some value $k$, and decides whether or not $x$'s value is always equal to $k$ whenever $T$ is executed.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162155987.png)

[^f1]: From this point on, we only consider Turing complete languages.

We could then exploit this analyzer to also decide the halting problem by using as input the following program where TM(j) simulates the j'th Turing machine on empty input:
![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162156424.png)
Here x has a constant value 17 if and only if the j'th Turing machine does not halt on empty input. If the hypothetical constant-value analyzer $A$ exists, then we have a decision procedure for the halting problem, which is known to be impossible [13].

At first, this seems like a discouraging result, however, this theoretical result does not prevent _approximative_ answers. While it is impossible to build an analysis that would correctly decide a property for any analyzed program, it is often possible to build analysis tools that give useful answers for most realistic programs. As the ideal analyzer does not exist, there is always room for building more precise approximations (which is colloquially called the _full employment theorem for static program analysis designers_).

Approximative answers may be useful for finding bugs in programs, which may be viewed as a weak form of program verification. As a case in point, consider programming with pointers in the C language. This is fraught with dangers such as null dereferences, dangling pointers, leaking memory, and unintended aliases. Ordinary compilers offer little protection from pointer errors. Consider the following small program which may perform every kind of error:

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162240565.png)

Standard compiler tools such as `gcc -Wall` detect no errors in this program. Finding the errors by testing might miss the errors (for this program, no errors are encountered unless we happen to have a test case that runs the program with exactly 42 arguments). However, if we had even approximative answers to questions about null values, pointer targets, and branch conditions then many of the above errors could be caught statically, without actually running the program.

**Exercise 1.1**: Describe all the pointer-related errors in the above program.

Ideally, the approximations we use are conservative (or safe), meaning that all errors lean to the same side, which is determined by our intended application. As an example, approximating the memory usage of programs is conservative if the estimates are never lower than what is actually possible when the programs are executed. Conservative approximations are closely related to the concept of soundness of program analyzers. We say that a program analyzer is sound if it never gives incorrect results (but it may answer maybe). Thus, the notion of soundness depends on the intended application of the analysis output, which may cause some confusion. For example, a verification tool is typically called sound if it never misses any errors of the kinds it has been designed to detect, but it is allowed to produce spurious warnings (also called false positives), whereas an automated testing tool is called sound if all reported errors are genuine, but it may miss errors.

Program analyses that are used for optimizations typically require soundness. If given false information, the optimization may change the semantics of the program. Conversely, if given trivial information, then the optimization fails to do anything.

Consider again the problem of determining if a variable has a constant value. If our intended application is to perform constant propagation optimization, then the analysis may only answer yes if the variable really is a constant and must answer maybe if the variable may or may not be a constant. The trivial solution is of course to answer maybe all the time, so we are facing the engineering challenge of answering yes as often as possible while obtaining a reasonable analysis performance.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162243897.png)

In the following chapters we focus on techniques for computing approximations that are conservative with respect to the semantics of the programming language. The theory of semantics-based abstract interpretation presented in Chapter 12 provides a solid mathematical framework for reasoning about analysis soundness and precision. Although soundness is a laudable goal in analysis design, modern analyzers for real programming languages often cut corners by sacrificing soundness to obtain better precision and performance, for example when modeling reflection in Java [15].

## 1.3 Undecidability of Program Correctness

(This section requires familiarity with the concept of universal Turing machines; it is not a prerequisite for the following chapters.)

The reduction from the halting problem presented above shows that some static analysis problems are undecidable. However, halting is often the least of the concerns programmers have about whether their programs work correctly. For example, if we wish to ensure that the programs we write cannot crash with null pointer errors, we may be willing to assume that the programs do not also have problems with infinite loops.

Using a diagonalization argument we can show a very strong result: It is impossible to build a static program analysis that can decide whether a given program may fail when executed. Moreover, this result holds even if the analysis is only required to work for programs that halt on all inputs. In other words, the halting problem is not the only obstacle; approximation is inevitably necessary.

If we model programs as deterministic Turing machines, program failure can be modeled using a special _fail_ state.[^f2] That is, on a given input, a Turing machine will eventually halt in its accept state (intuitively returning "yes"), in its reject state (intuitively returning "no"), in its fail state (meaning that the correctness condition has been violated), or the machine diverges (i.e., never halts). A Turing machine is _correct_ if its fail state is unreachable.

[^f2]: Technically, we here restrict ourselves to safety properties; liveness properties can be addressed similarly using other models of computability.

We can show the undecidability result using an elegant proof by contradiction. Assume $P$ is a program that can decide whether or not any given total Turing machine is correct. (If the input to $P$ is not a total Turing machine, $P^{\prime}$s output is unspecified - we only require it to correctly analyze Turing machines that always halt.) Let us say that $P$ halts in its accept state if and only if the given Turing machine is correct, and it halts in the reject state otherwise. Our goal is to show that $P$ cannot exist.

If $P$ exists, then we can also build another Turing machine, let us call it $M$, that takes as input the encoding $e(T)$ of a Turing machine $T$ and then builds the encoding $e(S_{T})$ of yet another Turing machine $S_{T}$, which behaves as follows: $S_{T}$ is essentially a universal Turing machine that is specialized to simulate $T$ on input $e(T)$. Let $w$ denote the input to $S_{T}$. Now $S_{T}$ is constructed such that it simulates $T$ on input $e(T)$ for at most $|w|$ moves. If the simulation ends in $T$'s accept state, then $S_{T}$ goes to its fail state. It is obviously possible to create $S_{T}$ in such a way that this is the only way it can reach its fail state. If the simulation does not end in $T$'s accept state (that is, $|w|$ moves have been made, or the simulation reaches $T$'s reject or fail state), then $S_{T}$ goes to its accept state or its reject state (which one we choose does not matter). This completes the explanation of how $S_{T}$ works relative to $T$ and $w$. Note that $S_{T}$ never diverges, and it reaches its fail state if and only if $T$ accepts input $e(T)$ after at most $|w|$ moves. After building $e(S_{T})$, $M$ passes it to our hypothetical program analyzer $P$. Assuming that $P$ works as promised, it ends in accept if $S_{T}$ is correct, in which case we also let $M$ halt in its accept state, and in reject otherwise, in which case $M$ similarly halts in its reject state.

![image.png](https://blog-1314253005.cos.ap-guangzhou.myqcloud.com/202311162243236.png)

We now ask: Does $M$ accept input $e(M)$? That is, what happens if we run $M$ with $T=M$? If $M$ does accept input $e(M)$, it must be the case that $P$ accepts input $e(S_{T})$, which in turn means that $S_{T}$ is correct, so its fail state is unreachable. In other words, for any input $w$, no matter its length, $S_{T}$ does not reach its fail state. This in turn means that $T$ does not accept input $e(T)$. However, we have $T=M$, so this contradicts our assumption that $M$ accepts input $e(M)$. Conversely, if $M$ rejects input $e(M)$, then $P$ rejects input $e(S_{T})$, so the fail state of $S_{T}$ is reachable for some input $v$. This means that there must exist some $w$ such that the fail state of $S_{T}$ is reached in $|w|$ steps on input $v$, so $T$ must accept input $e(T)$, and again we have a contradiction. By construction $M$ halts in either accept or reject on any input, but neither is possible for input $e(M)$. In conclusion, the ideal program correctness analyzer $P$ cannot exist.

**Exercise 1.2**: In the above proof, the hypothetical program analyzer $P$ is only required to correctly analyze programs that always halt. Show how the proof can be simplified if we want to prove the following weaker property: There exists no Turing machine $P$ that can decide whether or not the fail state is reachable in a given Turing machine. (Note that the given Turing machine is now not assumed to be total.)
