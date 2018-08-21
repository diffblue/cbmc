\ingroup module_hidden 
\page background-concepts Background Concepts

\author Martin Brain, Peter Schrammel, Johannes Kloos

The purpose of this section is to explain several key concepts used throughout
the CPROVER framework at a high level, ignoring the details of the actual implementation.
In particular, we will discuss different ways to represent programs in memory,
three important analysis methods and some commonly used terms.

\section representations_section Representations

One of the first questions we should be considering is how we represent programs
in such a way that we can easily analyze and reason about them.

As it turns out, the best way to do this is to use a variety of
different representations, each representing a different level of
abstraction. These representations are designed in such a way that for
each analysis we want to perform, there is an appropriate
representation, and it is easy to go from representations that are
close to the source code to representations that focus on specific
semantic aspects of the program.

The representations that the CPROVER framework uses mirror those
used in modern compilers such as LLVM and gcc. I will point out those
places where the CPROVER framework does things differently, attempting to give
rationales wherever possible.

One in-depth resource for most of this section is the classic
[compiler construction text book ''Compilers: Principles, Techniques and Tools''](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools)
by Aho, Lam, Sethi and Ullman.

To illustrate the different concepts, we will consider a small example
program. While the program is in C, the general ideas apply to other
languages as well - see later sections of this manual to understand how
the specific features of those languages are handled. Our running
example will be a program that calculates factorials.

```C
/* factorial.c
 *
 * For simplicity's sake, we just give the forward
 * declarations of atoi and printf.
 */
int atoi(const char *);
int printf(const char *, ...);

unsigned long factorial(unsigned n) {
  unsigned long fac = 1;
  for (unsigned int i = 1; i <= n; i++) {
    fac *= i;
  }
  return fac;
}

/* Error handling elided - this is just for illustration. */
int main(int argc, const char **argv) {
  unsigned n = atoi(argv[1]);
  printf("%u! = %lu\n", n, factorial(n));
  return 0;
}
```

The question of this first section is: how do we represent this program
in memory so that we can do something useful with it?

One possibility would be to just store the program as a string, but this
is clearly impractical: even finding whether there is an assignment to a
specific variable would require significant parsing effort. For this
reason, the first step is to parse the program text into a more abstract
representation.

\subsection AST_section AST

The first step in representing a program in memory is to parse the
program, at the same time checking for syntax errors, and store the
parsing result in memory.

The key data structure that stores the result of this step is known as an
**Abstract Syntax Tree**, or **AST** for short
(cf. [Wikipedia](https://en.wikipedia.org/wiki/Abstract_syntax_tree)).
ASTs are still relatively
close to the source code, and represent the structure of the source code
while abstracting away from syntactic details, e.g., dropping
parentheses, semicolons and braces as long as those are only used for
grouping.

Considering the example of the C program given above, we first notice
that the program describes (in C terms) a single *translation unit*,
consisting of four top-level *declarations* (the two function forward
declarations of `atoi` and `printf`, and the function definitions of
`factorial` and `main`). Let us start considering the specification of
`atoi`. This gives rise to a subtree modeling that we have a function
called `atoi` whose return type is `int`, with an unnamed argument of type
`const char *`. We can represent this using a tree that has, for instance, the
following structure (this is a simplified version of the tree that the CPROVER framework
uses internally):

\dot "AST for the `atoi` declaration"
digraph ast {
        global [label="Global - code\nType: int\nName: atoi",shape=rectangle]
        parameters [label="Parameters",shape=rectangle]
        parameter0 [label="Parameter\nType: const char *",shape=rectangle]
        global -> parameters -> parameter0
}
\enddot

This graph shows the (simplified) AST structure for the `atoi` function.
The top level says that this is a global entity, namely one that has
code (i.e., a function), called `atoi` and yielding `int`. Furthermore,
it has a child node initiating a parameter list, and there is a node in
the parameter list for each parameter, giving its type and name, if a
name is given.

Extending this idea, we can represent the structure of the `factorial`
function using ASTs. The idea here is that the code itself has a
hierarchical structure. In the case of C, this starts with the block
structure of the code: at the top, we start with a block of code, having
three children, each being a ''statement'' node:
1. `unsigned long fac = 1`
2. `for (unsigned int i = 1; i <= n; i++) { fac *= i }`
3. `return fac`

The first statement is already a basic statement: we represent it as a
local declaration (similar to the global declarations above) of a
variable.

\dot "AST for `unsigned long fac = 1`"
digraph ast {
        global [label="Code\nStatement: Declaration\nType: unsigned long\nName: fac\nInitial Value: 1",shape=rectangle]
}
\enddot

The second statement is a compound statement, which we can decompose
further. At the top level, we have a node stating that this is a `for`
statement, with four child nodes:
1. Another declaration node, declaring variable `i`.
2. An expression node, with operator `<=` and two children
   giving the LHS as variable `i` and the RHS as variable `n`.
3. An expression node with post-fix operator `++` and a child
   giving the variable `i` as argument.
4. A block node, starting a new code block. This node has one child:
   1. An expression node with top-level operator `*=` and two child
      nodes giving the LHS as variable `fac` and the RHS as variable
      `i`.
All in all, the AST for this piece of code looks like this:

\dot "AST for the `for` loop"
digraph ast {
        node [shape=rectangle]
        for [label="Code\nStatement: for"]
        decli [label="Code\nStatement: Declaration\nType: unsigned\nName: i\nInitial Value: 1"]
        cond [label="Expression: <="]
        condlhs [label="Expression: Variable i"]
        condrhs [label="Expression: Variable n"]
        inc [label="Code\nExpression: ++ - postfix"]
        incarg [label="Expression: Variable i"]
        body [label="Code\nStatement: Block"]
        mult [label="Code\nExpression: *="]
        multlhs [label="Expression: Variable fac"]
        multrhs [label="Expression: Variable i"]
        for -> {decli,cond,inc,body}
        cond -> {condlhs,condrhs}
        inc -> incarg
        body -> mult -> {multlhs, multrhs}
}
\enddot

Finally, the third statement is again simple: it consists of a return
statement node, with a child node for the variable expression `fac`.
Since the AST is very similar to the first AST above, we omit it here.
All in all, the AST for the function body looks like this:

\dot "AST for the body of `factorial`"
digraph ast {
        node [shape=rectangle]
        factorial [label="Code\nStatement: Block"]
        declfac [label="Code\nStatement: Declaration\nType: unsigned long\nName: fac\nInitial Value: 1"]
        for [label="Code\nStatement: for"]
        decli [label="Code\nStatement: Declaration\nType: unsigned\nName: i\nInitial Value: 1"]
        cond [label="Expression: <="]
        condlhs [label="Expression: Variable i"]
        condrhs [label="Expression: Variable n"]
        inc [label="Code\nExpression: ++ - postfix"]
        incarg [label="Expression: Variable i"]
        body [label="Code\nStatement: Block"]
        mult [label="Code\nExpression: *="]
        multlhs [label="Expression: Variable fac"]
        multrhs [label="Expression: Variable i"]
        return [label="Code\nStatement: return"]
        returnexpr [label="Expression: Variable fac"]
        factorial -> {declfac, for, return}
        for -> {decli,cond,inc,body}
        cond -> {condlhs,condrhs}
        inc -> incarg
        body -> mult -> {multlhs, multrhs}
        return -> returnexpr
}
\enddot

Using the AST for the function body, we can easily produce the
definition of the `factorial` function:

\dot "AST for `factorial` (full definition)"
digraph ast {
        node [shape=rectangle]
        globalfactorial [label="Global - code\nType: unsigned long\nName: factorial"]
        parameters [label="Parameters"]
        parameter [label="Parameter\nType: unsigned\nName: n"]
        factorial [label="Code\nStatement: Block"]
        declfac [label="Code\nStatement: Declaration\nType: unsigned long\nName: fac\nInitial Value: 1"]
        for [label="Code\nStatement: for"]
        decli [label="Code\nStatement: Declaration\nType: unsigned\nName: i\nInitial Value: 1"]
        cond [label="Expression: <="]
        condlhs [label="Expression: Variable i"]
        condrhs [label="Expression: Variable n"]
        inc [label="Code\nExpression: ++ - postfix"]
        incarg [label="Expression: Variable i"]
        body [label="Code\nStatement: Block"]
        mult [label="Code\nExpression: *="]
        multlhs [label="Expression: Variable fac"]
        multrhs [label="Expression: Variable i"]
        return [label="Code\nStatement: return"]
        returnexpr [label="Expression: Variable fac"]
        factorial -> {declfac, for, return}
        for -> {decli,cond,inc,body}
        cond -> {condlhs,condrhs}
        inc -> incarg
        body -> mult -> {multlhs, multrhs}
        return -> returnexpr
        globalfactorial -> {parameters,factorial}
        parameters -> parameter
}
\enddot

In the end, we produce a sequence of trees modeling each declaration
in the translation unit (i.e., the file `factorial.c`).

This data structure is already useful: at this level, we can easily
derive simple information such as ''which functions are being defined?'',
''what are the arguments to a given function'' and so on.

\subsubsection symbol_table_section Symbol tables and variable disambiguation

Nevertheless, for many analyses, this representation needs to be
transformed further. In general, the first step is to **resolve variable
names**. This is done using an auxiliary data structure known as the
**symbol table**.

The issue that this step addresses is that the meaning of a variable
name depends on a given *scope* - for instance, in a C program, we can
define the variable `i` as a local variable in two different functions,
so that the name `i` refers to two different objects, depending on which
function is being executed at a given point in time.

To resolve this problem, a first transformation step is performed,
changing (short) variable names to some form of unique identifier. This
ensures that each variable identifier is used only once, and all
accesses to a given variable can be easily found by just looking for the
variable identifier. For instance, we could change each variable name
into a pair of the name and a serial number. The serial number gets
increased whenever a variable of that name is declared. In the example,
the ASTs for `factorial` and `main` after resolving variable names would
look roughly like this:

\dot "ASTs with resolved variables"
digraph ast {
        node [shape=rectangle]
        globalfactorial [label="Global - code\nType: unsigned long\nName: factorial"]
        parameters [label="Parameters"]
        parameter [label="Parameter\nType: unsigned\nName: n.1"]
        factorial [label="Code\nStatement: Block"]
        declfac [label="Code\nStatement: Declaration\nType: unsigned long\nName: fac.1\nInitial Value: 1"]
        for [label="Code\nStatement: for"]
        decli [label="Code\nStatement: Declaration\nType: unsigned\nName: i.1\nInitial Value: 1"]
        cond [label="Expression: <="]
        condlhs [label="Expression: Variable i.1"]
        condrhs [label="Expression: Variable n.1"]
        inc [label="Code\nExpression: ++ - postfix"]
        incarg [label="Expression: Variable i.1"]
        body [label="Code\nStatement: Block"]
        mult [label="Code\nExpression: *="]
        multlhs [label="Expression: Variable fac.1"]
        multrhs [label="Expression: Variable i.1"]
        return [label="Code\nStatement: return"]
        returnexpr [label="Expression: Variable fac.1"]
        factorial -> {declfac, for, return}
        for -> {decli,cond,inc,body}
        cond -> {condlhs,condrhs}
        inc -> incarg
        body -> mult -> {multlhs, multrhs}
        return -> returnexpr
        globalfactorial -> {parameters,factorial}
        parameters -> parameter

        globalmain [label="Global - code\nType: int\nName: main"]
        parametersmain [label="Parameters"]
        parameterargc [label="Parameter\nType: int\nName: argc.1"]
        parameterargv [label="Parameter\nType: const char **\nName: argv.1"]
        mainbody [label="Code\nStatement: Block"]
        main0 [label="Code\nStatement: Declaration\nType: unsigned\nName: n.2\nInitial Value: Expression"]
        main1 [label="Code\nExpression: Call"]
        main1fun [label="Expression: Global atoi"]
        main1arg [label="Arguments"]
        main1arg1 [label="Expression: Index"]
        main1arg11 [label="Expression: Variable argv.1"]
        main1arg12 [label="Expression: 1"]
        main2 [label="Code\nExpression: Call"]
        main2fun [label="Expression: Global printf"]
        main2arg [label="Arguments"]
        main2arg1 [label="Expression: ..."]
        main2arg2 [label="Expression: Variable n.2"]
        main2arg3 [label="Expression: Call"]
        main2arg3fun [label="Expression: Global factorial"]
        main2arg3arg [label="Arguments"]
        main2arg3arg1 [label="Expression: Variable n.2"]
        main3 [label="Code\nStatement: return"]
        main3expr [label="Expression: 0"]
        globalmain -> {parametersmain,mainbody}
        parametersmain -> {parameterargc, parameterargv}
        mainbody -> {main0,main1,main2}
        main1 -> {main1fun, main1arg}
        main1arg -> main1arg1 -> {main1arg11,main1arg12}
        main2 -> {main2fun, main2arg}
        main2arg -> {main2arg1,main2arg2,main2arg3}
        main2arg3-> {main2arg3fun, main2arg3arg}
        main2arg3arg -> main2arg3arg1
        main3 -> mainexpr
}
\enddot

Note that the parameter `n` in `factorial` and the local variable `n` in
`main` are now disambiguated as `n.1` and `n.2`; furthermore, we leave
the names of global objects as-is. In the CPROVER framework, a more
elaborate system is used: local variables are prefixed with the function names,
and further disambiguation is performed by adding indices. For brevity,
we use indices only.

Further information on ASTs can be found in the
[Wikipedia page](https://en.wikipedia.org/wiki/Abstract_syntax_tree)
and the materials linked there. Additionally, there is an
[interesting discussion on StackOverflow](https://stackoverflow.com/questions/1888854/what-is-the-difference-between-an-abstract-syntax-tree-and-a-concrete-syntax-tree)
about abstract versus concrete syntax trees.

At this level, we can already perform a number of interesting analyses,
such as basic type checking. But for more advanced analyses, other
representations are better: the AST contains many different kinds of nodes
(essentially, one per type of program construct), and has a rather
intricate structure.

\subsection IR_section Intermediate Representations (IR)

The ASTs in the previous section represent the syntax of a program, including
all the features of a given programming language. But in practice, most
programming languages have a large amount of ''syntactic sugar'': constructs
that are, technically speaking, redundant, but make programming a lot easier.
For analysis, this means that if we immediately try to work on the initial
AST, we would have to handle all these various cases.

To simplify analysis, it pays off to bring the AST into simpler forms,
known as **intermediate representations** (short **IR**). An IR is usually
given as some form of AST, using a more restricted subset or a variant of the
original language that is easier to analyze than the original version.

Taking the example from above, we rewrite the program into a simpler form of
the C language: instead of allowing powerful control constructs such as
`while` and `for`, we reduce everything to `if` and `goto`. In fact, we even
restrict `if` statements: an `if` statement should always be of the form
`if (*condition*) goto *target* else goto *target*;`. As it turns out, this is
sufficient to represent every C program. The factorial function in our
example program can then be rewritten as follows:

```C
unsigned long factorial(unsigned n) {
  unsigned long fac = 1;
  // Replace the for loop with if and goto
  unsigned int i = 1;
for_loop_start:
  if (i <= n) goto for_loop_entry else goto for_loop_end;
for_loop_entry:
    fac *= i;
    i++;
    goto for_loop_start;
for_loop_end:
  return fac;
}
```

We leave it up to the reader to verify that both versions of the function
behave the same way, and to draw the function as an AST.

In the CPROVER framework, a number of different IRs are employed to
simplify the program under analysis into a simple core language step-by-step.
In particular, expressions are brought into much simpler forms.
This sequence of transformations is described in later chapters.

TODO: Link to corresponding sections.

\subsection CFG_section Control Flow Graphs (CFG)

Another important representation of a program can be gained by transforming
the program structure into a
[**control flow graph**](https://en.wikipedia.org/wiki/Control_flow_graph),
short **CFG**. While the
AST focuses more on the syntactic structure of the program, keeping
constructs like while loops and similar forms of structured control flow,
the CFG uses a unified graph representation for control flow. 

In general, for analyses based around Abstract Interpretation
(see \ref abstract_interpretation_section), it
is usually preferable to use a CFG representation, while other analyses,
such as variable scope detection, may be easier to perform on ASTs.

The general idea is to present the program as a graph. The nodes of the graph
are instructions or sequences of instructions. In general, the nodes are
**basic blocks**: a basic block is a sequence of statements that is always
executed in order from beginning to end. The edges of the graph describe how
the program execution may move from one basic block to the next.
Note that single statements are always basic blocks; this is the representation
used inside the CPROVER framework. In the examples below, we try to use maximal
basic blocks (i.e., basic blocks that are as large as possible); this can be
advantageous for some analyses.

Let us consider the factorial function as an example. As a reminder,
here is the code, in IR:
```C
  unsigned long fac = 1;
  unsigned int i = 1;
for_loop_start:
  if (i <= n) goto for_loop_entry else goto for_loop_end;
for_loop_entry:
    fac *= i;
    i++;
    goto for_loop_start;
for_loop_end:
  return fac;
```

We rewrite the code with disambiguated variables (building the
AST from it is left as an exercise):
```C
  unsigned long fac.1 = 1;
  unsigned int i.1 = 1;
for_loop_start:
  if (i.1 <= n.1) goto for_loop_entry else goto for_loop_end;
for_loop_entry:
    fac.1 *= i.1;
    i.1++;
    goto for_loop_start;
for_loop_end:
  return fac.1;
```

This function consists of four basic blocks:
1. `unsigned long fac.1 = 1;`
   `unsigned int i.1 = 1;`
2. `if (i.1 <= n.1) goto for_loop_entry else goto for_loop_end`
   (this block has a label, `for_loop_start`).
3. `fac.1 *= i.1`<br/>
   `i.1 ++`
   `goto for_loop_start`
   (this block has a label, `for_loop_entry`).
4. `return fac.1`
   (this block has a label, `for_loop_end`).

One way to understand which functions form basic blocks is to consider the
successors of each instruction. If we have two instructions A and B, we say
that B is a *successor* of A if, after executing A, we can execute B without any
intervening instructions. For instance, in the example above, the loop
initialization statement `unsigned long int i.1 = 1` is a successor of
`unsigned long fac.1 = 1`. On the other hand, `return fac.1` is not a successor
of `unsigned long fac.1 = 1`: we always have to execute some other intermediate
statements to reach the return statement.

Now, consider the `if` statement,
`if (i.1 <= n.1) goto for_loop_entry else goto for_loop_end`.
This statement has *two* successors: `fac.1 *= i.1` and `return fac.1`.

Similarly, we say that A is a *predecessor* of B if B is a successor of A.
We find that the `if` statement has two predecessors,
`unsigned int i.1 = 1` and `goto for_loop_start`.

A basic block is a sequence of instructions with the following property:
1. If B comes directly after A in the sequence, B must be the sole successor of A.
2. If A comes directly before B in the sequence, A must be the sole predecessor of B.

In particular, each member of the sequence but the first must have exactly one
predecessor, and each member of the sequence but the last must have exactly one
successor.
These criteria explain why we have the basic blocks described above.

Putting everything together, we get a control flow graph like this:

\dot "Control flow graph for factorial"
digraph cfg {
  node [shape=rectangle]
  bb1 [label="Declaration: unsigned long fac.1, value 1\nDeclaration: unsigned i.1, value 1",peripheries=2]
  bb2 [label="Expression: i.1 <= n.1"]
  bb3 [label="Expression: fac.1 *= i.1\nExpression: i.1 ++",junk="*"]
  
  bb4 [label="Return: fac.1",style=filled,fillcolor=gray80]
  {bb1, bb3} -> bb2
  bb2 -> bb3 [label="true"]
  bb2 -> bb4 [label="false"]
}
\enddot


The graph can be read as follows: each node corresponds to a basic
block. The initial basic block (where the function is entered) is marked
with a double border, while those basic blocks that leave the function
have a gray background. An edge from a basic block B to a basic block B',
means that if the execution reaches the end of B, execution may continue in B'.
Some edges are labeled: the edge leaving the comparison
basic block with the label `true`, for instance, can only be taken if
the comparison did, in fact, return `true`.

Note that this representation makes it very easy to interpret the
program, keeping just two pieces of state: the current position (which
basic block and which line), and the values of all variables (in real
software, this would also include parts of the heap and the call stack).
Execution proceeds as follows: as long as there are still instructions
to execute in the current basic block, run the next instruction and move
the current position to right after that instruction. At the end of a
basic block, take one of the available outgoing edges to another basic block.

In the CPROVER framework, we often do not construct CFGs explicitly, but instead
use an IR that is constructed in a way very similar to CFGs, known as 
''GOTO programs''. This IR is used to implement a number
of static analyses, as described in sections \ref analyses-frameworks
and \ref analyses-specific-analyses.

\subsection SSA_section SSA

While control flow graphs are already quite useful for static analysis,
some techniques benefit from a further transformation to a
representation know as **static single assignment**, short **SSA**. The
point of this step is to ensure that we can talk about the entire history
of assignments to a given variable. This is achieved by renaming
variables again: whenever we assign to a variable, we *clone* this
variable by giving it a new name. This ensures that each variable
appearing in the resulting program is written to exactly once (but it
may be read arbitrarily many times). In this
way, we can refer to earlier values of the variable by just referencing
the name of an older incarnation of the variable.

We illustrate this transformation by first showing how the body of the
`for` loop of `factorial` is transformed. We currently have:

```
expression: fac.1 *= i.1
expression: i.1 ++
```

We now give a second number to each variable, counting the number of
assignments so far. Thus, the SSA version of this code turns out to be
```
expression: fac.1.2 = fac1.1 * i.1.1
expression: i.1.2 = i.1.1 + 1
```
This representation now allows us to state facts such as
''`i` is increasing'' by writing `i.1.1 < i.1.2`.

At this point, we run into a complication. Consider the following piece
of code for illustration:
```C
// Given some integers a, b
int x = a;
if (a < b)
  x = b;
return x;
```
The corresponding control flow graph looks like this:

\dot "CFG for maximum function"
digraph ast {
  node [shape=rectangle]
  first [label="declare x\nx = a\na < b"]
  second [label="x = b"]
  third [label="return x"]
  first -> second [label="true"]
  first -> third [label="false"]
  second -> third
}
\enddot

When we try to transform to SSA, we get:
\dot "CFG for maximum function - SSA, attempt"
digraph ast {
  node [shape=rectangle]
  first [label="\nx.1 = a\na < b"]
  second [label="x.2 = b"]
  third [label="return ???"]
  first -> second [label="true"]
  first -> third [label="false"]
  second -> third
}
\enddot
Depending on which path the execution takes, we have to return either
`x.1` or `x.2`! The way to make this work is to introduce a function
&Phi; that selects the right instance of the variable; in the
example, we would have
\dot "CFG for maximum function - SSA using &Phi;"
digraph ast {
  node [shape=rectangle]
  first [label="\nx.1 = a\na < b"]
  second [label="x.2 = b"]
  third [label="return &Phi;(x.1,x.2)"]
  first -> second [label="true"]
  first -> third [label="false"]
  second -> third
}
\enddot

In the CPROVER framework, we provide a precise implementation of &Phi;, using explicitly tracked
information about which branches were taken by the program.
There are also some differences in how loops are
handled (finite unrolling in CPROVER, versus a &Phi;-based approach in
compilers); this approach will be discussed in a later chapter.

For the time being, let us come back to `factorial`. We can now give
an SSA using &Phi; functions:

\dot "Control flow graph in SSA for factorial"
digraph cfg {
  node [shape=rectangle]
  bb1 [label="unsigned long fac.1.1 = 1\nunsigned i.1.1 = 1",peripheries=2]
  bb2 [label="i.1.2 = &Phi;(i.1.1, i.1.3)\nfac.1.2 = &Phi;(i.1.1, i.1.3)\ni.1.2 <= n.1.1"]
  bb3 [label="fac.1.3 = fac.1.2 * i.1.2\ni.1.3 = i.1.2 + 1"]
  
  bb4 [label="Return fac.1.2",style=filled,fillcolor=gray80]
  {bb1, bb3} -> bb2
  bb2 -> bb3 [label="true"]
  bb2 -> bb4 [label="false"]
}
\enddot

The details of SSA construction, plus some discussion of how it is
used in compilers, can be found in the
[original paper](https://dl.acm.org/citation.cfm?doid=115372.115320).

The SSA is an extremely helpful representation when one
wishes to perform model checking on the program (see next section),
since it is much easier to extract the logic formulas used in this
technique from an SSA compared to a CFG (or, even worse, an AST). That
being said, the CPROVER framework takes a different route, opting to convert to
intermediate representation known as GOTO programs instead.

\section analysis_techniques_section Analysis techniques

\subsection BMC_section Bounded model checking

One of the most important analysis techniques by the CPROVER framework,
implemented using the CBMC (and JBMC) tools, is **bounded model checking**,
a specific instance of a method known as
[Model Checking](https://en.wikipedia.org/wiki/Model_checking).

The basic question that model checking tries to answer is: given some system
(in our case, a program) and some property, can we find an execution of the
system such that it reaches a state where the property holds?
If yes, we would like to know how the program reaches this state - at the very
least, we want to see what inputs are required, but in general, we would prefer
having a **trace**, which shows what statements are executed and in which order.

In general, a trace describes which statements of the program were executed,
and which intermediate states were reached. Often, it is sufficient to
only provide part of the intermediate states (omitting some entirely, and
only mentioning parts that cannot be easily reconstructed in others).

As it turns out, model checking for programs is, in general, a hard problem.
Part of the reason for this is that many model checking algorithms strive for
a form of ''completeness'' where they either find a trace or return a proof
that such a trace cannot possibly exist.

Since we are interested in generating test cases, we prefer a different
approach: it may be that a certain target state is reachable only after
a very long execution, or not at all, but this information does not help
us in constructing test cases. For this reason, we introduce an
**execution bound** that describes how deep we go when analyzing a program.

Model checking techniques using such execution bounds are known as
**bounded model checking**; they will return either a trace, or a statement
that says ''the target state could not be reached in n steps'', for a
given bound n. Thus, for a given bound, we always get an
**underapproximation** of all states that can be reached: we
can certainly find those reachable within the given bound, but we may
miss states that can be reached only with more steps. Conversely, we will
never claim that a state is not reachable within a certain bound if there is,
in fact, a way of reaching this state.

The bounded model checking techniques used by the CPROVER framework are
based on *symbolic model checking*, a family of model checking techniques that
work on sets of program states and use advanced tools such as SAT solvers (more
on that below) to calculate the set of reachable states. The key step here
is to encode both the program and the set of states using an appropriate logic,
mostly *propositional logic* and (fragments of) *first-order logic*.

In the following, we will quickly discuss propositional logic, in combination
with SAT solving, and show how to build a simple bounded model checker for
a finite-state program. Actual bounded model checking for software requires
a number of additional steps and concepts, which will be introduced as required
later on.

\subsubsection propositional_logic_subsubsection Propositional logic and SAT solving

Many of the concepts in this section can be found in more detail in the
Wikipedia article on [Propositional logic](https://en.wikipedia.org/wiki/Propositional_calculus).

Let us start by looking at **propositional formulas**. A propositional formula
consists of **propositional variables**, say *x*, *y* and *z*, that can
take the Boolean values **true** and **false**, connected together with
logical operators (often called *junctors*), namely *and*, *or* and *not*.
Sometimes, one introduces additional junctors, such as *xor* or *implies*,
but these can be defined in terms of the three basic junctors just described.

Examples of propositional formulas would be ''*x* and *y*'' or
''not *x* or *y* or *z*''. We can **evaluate** formulas by setting each
variable to a Boolean value and reducing using the follows rules:
- *x* and **false** = **false** and *x* = **false** or **false** = not **true** = **false**
- *x* or **true** = **true** or *x* = **true** and **true** = not **false** = **true**

An important related question is: given a propositional formula,
is there a variable assignment that makes it evaluate to true?
This is known as the [**SAT problem**](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem).
The most important things to know about SAT are:
1. It forms the basis for bounded model checking algorithms;
2. It is a very hard problem to solve in general: it is NP-complete,
   meaning that it is easy to check a solution, but (as far as we know) hard
   to find one;
3. There has been impressive research in
  [**SAT solvers**](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem#Algorithms_for_solving_SAT)
  that work well in practice for the kinds of formulas that we encounter in
  model checking. A commonly-used SAT solver is [minisat](http://minisat.se).
4. SAT solvers use a specific input format for propositional formulas, known
  as the [**conjunctive normal form**](https://en.wikipedia.org/wiki/Conjunctive_normal_form).
  For details, see the linked Wikipedia page;
  roughly, a conjunctive normal form formula is a propositional
  formula with a specific shape: at the lowest level are
  *atoms*, which are propositional variables ''*x*'' and
  negated propositional variables ''not *x*'';
  the next layer above are *clauses*, which are sequences
  of atoms connected with ''or'', e.g. ''not *x* or *y* or *z*''.
  The top layer consists sequences of clauses,
  connected with ''and''.

As an example in how to use a SAT solver, consider the following
formula (in conjunctive normal form):

''(*x* or *y*) and (*x* or not *y*) and *x* and *y*''

We can represent this formula in the minisat input format as:

```
p cnf 2 3
1 2 0
1 -2 0
1 0
2 0
```
Compare the [Minisat user guide](https://www.dwheeler.com/essays/minisat-user-guide.html).
Try to run minisat on this example. What would you expect, and what result do you get?

Next, try running minisat on the following formula:
''(*x* or *y*) and (*x* or not *y*) and (not *x*) and *y*''
What changed? Why?

\subsubsection bmc_subsubsection How bounded model checking works

TODO This section needs to be written on the next documentation day.

The following content needs to be added:

- How does it work? Encoding of state as propositions/first-order
  propositions, step function and composition of step functions.
- Solve question: is there a model for this formula?
- Traces

\subsubsection smt_etc_subsubsection Where to go from here

The above section gives only a superficial overview on how SAT solving and
bounded model checking work. Inside the CPROVER framework, we use a
significantly more advanced engine, with numerous optimizations to the
basic algorithms presented above. One feature that stands out is that
we do not reduce everything to propositional logic, but instead use a more
powerful logic, namely quantifier-free first-order logic. The main
difference is that instead of propositional variables, we allow expressions
that return Boolean values, such as comparisons between numbers or string
matching expressions. This gives us a richer logic to express properties.
Of course, a simple SAT solver cannot deal with such formulas, which is why we
go to [*SMT solvers*](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
instead - these solvers can deal with specific classes
of first-order formulas (like the ones we produce).
One well-known SMT solver is [Z3](https://github.com/Z3Prover/z3).

\subsection static_analysis_section Static analysis

While BMC analyzes the program by transforming everything to logic
formulas and, essentially, running the program on sets of concrete
states, another approach to learn about a program is based on the idea
of interpreting an abstract version of the program. This is known
as [**abstract interpretation**](https://en.wikipedia.org/wiki/Abstract_interpretation).
Abstract interpretation is one of the
main methods in the area of **static analysis**.

\subsubsection abstract_interpretation_section Abstract Interpretation

The key idea is that instead of looking at concrete program states
(e.g., ''variable x contains value 1''), we look at some
sufficiently-precise abstraction (e.g., ''variable x is odd'', or
''variable x is positive''), and perform interpretation of the program
using such abstract values. Coming back to our running example, we wish
to prove that the factorial function never returns 0.

An abstract interpretation is made up from four ingredients:
1. An **abstract domain**, which represents the analysis results.
2. A family of **transformers**, which describe how basic programming
   language constructs modify the state.
3. A map that takes a pair of a program location (e.g., a position in the
   program code) and a variable name and yields a value in the abstract domain.
4. An algorithm to compute a ''fixed point'', computing a map as described
   in the previous step that describes the behavior of the program.

The first ingredient we need for abstract interpretation is the
**abstract domain**.
The domain allows us to express what we know about a given variable or
value at a given program location; in our example, whether it is zero or not.
The way we use the abstract domain is for each program point, we have a
map from visible variables to elements of the abstract domain,
describing what we know about the values of the variables at this point.

For instance, consider the `factorial` example again. After running the
first basic block, we know that `fac` and `i` both contain 1, so we have
a map that associates both `fac` and `i` to "not 0".

An abstract domain is a set $D$ (or, if you
prefer, a data type) with the following properties:
- There is a function merge that takes two elements of $D$ and returns
  an element of $D$. This function is associative (merge(x, merge(y,z))
  = merge(merge(x,y), z)), commutative (merge(x,y) = merge(y,x)) and
  idempotent (merge(x,x) = x).
- There is an element bottom of $D$ such that merge(x, bottom) = x.

Algebraically speaking, $D$ needs to be a semi-lattice.

For our example, we use the following domain:
- D contains the elements "bottom" (nothing is known),
  "equals 0", "not 0" and "could be 0".

- merge is defined as follows:
  merge(bottom, x) = x
  merge("could be 0", x) = "could be 0"
  merge(x,x) = x
  merge("equals 0", "not 0") = "could be 0"
- bottom is bottom, obviously.
It is easy but tedious to check that all conditions hold.

The second ingredient we need are the **abstract state transformers**.
An abstract state transformer describes how a specific expression or
statement processes abstract values. For the example, we need to define
abstract state transformers for multiplication and addition.

Let us start with multiplication, so let us look at the expression
`x*y`. We know that if `x` or `y` are 0, `x*y` is zero. Thus,
if `x` or `y` are "equals 0", the result of `x*y` is also "equals 0".
If `x` or `y` are "could be 0" (but neither is "equals 0"), we simply
don't know what the result is - it could be zero or not. Thus, in this
case, the result is "could be 0".

What if `x` and `y` are both "not 0"? In a mathematically ideal world,
we would have `x*y` be non-zero as well. But in a C program,
multiplication could overflow, yielding 0! So, to be correct, we have to
yield "could be 0" in this case.

Finally, when `x` is bottom, we can just return whatever value we had
assigned to `y`, and vice versa.

For addition, the situation looks like this: consider `x+y`.
If neither `x` nor `y` is "not 0", but
at least one is "could be 0", the result is "could be 0". If both are
"equals 0", the result is "equals 0". What if both are "not 0"? It seems
that, since the variables are unsigned and not zero, it should be
"not 0". Sadly, overflow strikes again, and we have to make do with
"could be 0". The bottom cases can be handled just like for
multiplication.

The way of defining the transformation functions above showcases another
important property: they must reflect the actual behavior of the
underlying program instructions. There is a formal description of this
property, using [*Galois connections*](https://en.wikipedia.org/wiki/Galois_connection);
for the details, it is best to
look at the literature.

The third ingredient is straightforward: we use a simple map
from program locations and variable names to values in the abstract
domain. In more complex analyses, more involved forms of maps may be
used (e.g., to handle arbitrary procedure calls, or to account for the
heap).

At this point, we have almost all the ingredients we need to set up an abstract
interpretation. To actually analyze a function, we take its CFG and
perform a *fixpoint algorithm*.

Concretely, let us consider the CFG for factorial again. This time, we
have named the basic blocks, and simplified the variable names.
\dot "Control flow graph for factorial - named basic blocks"
digraph cfg {
  node [shape=rectangle]
  bb1 [label="BB1\nDeclaration: unsigned long fac, value 1\nDeclaration: unsigned i, value 1",peripheries=2]
  bb2 [label="BB2\nExpression: i <= n"]
  bb3 [label="BB3\nExpression: fac *= i\nExpression: i ++",junk="*"]
  
  bb4 [label="BB4\nReturn: fac",style=filled,fillcolor=gray80]
  {bb1, bb3} -> bb2
  bb2 -> bb3 [label="true"]
  bb2 -> bb4 [label="false"]
}
\enddot

We provide an initial variable map: `n` is "could be 0" before BB1.
As a first step, we analyze BB1 and find that the final variable map
should be:
- `n` "could be 0".
- `fac` "not 0" (it is, in fact, 1, but our domain does not allow us to
  express this).
- `i` "not 0".
Let as call this state N.

At this point, we look at all the outgoing edges of BB1 - we wish to
propagate our new results to all blocks that follow BB1. There is only
one such block, BB2. We analyze BB2 and find that it doesn't change any
variables. Furthermore, the result of `i <= n` does not allow us
to infer anything about the values in the variable map, so we get the
same variable map at the end of BB2 as before.

Again, we look at the outgoing edges. There are two successor blocks,
BB3 and BB4. The information in our variable map does not allow us to
rule out either of the branches, so we need to propagate to both blocks.
We start with BB3 and remember that we need to visit BB4.

At this point, we know that `n` "could be 0", while `fac` and `i` are "not 0".
Applying the abstract transformers, we learn that afterwards, both `fac`
and `i` "could be 0" (`fac` ends up as "could be 0" since both `fac` and `i`
were "not 0" initially, `i` ends up as "could be 0" because both `i` and 1
are "not 0"). So, the final variable map at the end of BB3 is
- `n`, `fac` and `i` "could be 0".
Let us call this state S.

At this point, we propagate again, this time to BB2. But wait, we have
propagated to BB2 before! The way this is handled is as follows:
We first calculate what the result of running BB2 from S; this yields S
again. Now, we know that at the end of BB2, we can be either in state S
or N. To get a single state out of these two, we *merge*: for each
variable, merge the mapping of that variable in S and N.
We get:
- `n` maps to merge("could be 0", "could be 0") = "could be 0"
- `fac` maps to merge("could be 0", "not 0") = "could be 0"
- `i` maps to merge("could be 0", "not 0") = "could be 0"
In other words, we arrive at S again.

At this point, we propagate to BB3 and BB4 again. Running BB3, we again
end up with state S at the end of BB3, so things don't change. We detect
this situation and figure out that we do not need to propagate from BB3
to BB2 - this would not change anything! Thus, we can now propagate to
BB4. The state at the end of BB4 is also S.

Now, since we know the variable map at the end of BB4, we can look up
the properties of the return value: in S, `fac` maps to "could be 0", so
we could not prove that the function never returns 0. In fact, this is
correct: calculating `factorial(200)` will yield 0, since the 64-bit
integer `fac` overflows.

Nevertheless, let us consider what would happen in a mathematically ideal
world (e.g., if we used big integers). In that case, we would get
"not 0" * "not 0" = "not 0", "not 0" + x = "not 0" and
x + "not 0" = "not 0". Running the abstract interpretation with these
semantics, we find that if we start BB3 with variable map N, we get
variable map N at the end as well, so we end up with variable map N
at the end of BB4 - but this means that fac maps to "not 0"!

The algorithm sketched above is called a fixpoint algorithm because we
keep propagating until we find that applying the transformers does not
yield any new results (which, in a mathematically precise way, can be
shown to be equivalent to calculating, for a specific function f, an x such
that f(x) = x).

This overview only describes the most basic way of performing abstract
interpretation. For one, it only works on the procedure level (we say it is an
*intra-procedural analysis*); there are various ways of extending
it to work across function boundaries, yielding *inter-procedural analysis*.
Additionally, there are situations where it can be helpful make a variable map
more abstract (widening) or use information that can be gained from
various sources to make it more precise (narrowing); these advanced
topics can be found in the literature as well.

\section Glossary_section Glossary

\subsection instrument_subsection Instrument

To instrument a piece of code means to modify it by (usually) inserting new
fragments of code that, when executed, tell us something useful about the code
that has been instrumented.

For instance, imagine you are given the following function:
```C
int aha (int a)
{
   if (a > 10)
      return 1;
   else
      return -1;
}
```

and you want to design an analysis that figures out which lines of code will
be covered when `aha` is executed with the input `5`.

We can *instrument* the code so that the function will look like:
```C
int aha (int a)
{
   __runtime_line_seen(0);
   if (a > 10) {
      __runtime_line_seen(1);
      return 1;
   } else {
      __runtime_line_seen(2);
      return -1;
   }
   __runtime_line_seen(3);
}
```

All we have to do now is to implement the function
`void __runtime_line_seen(int line)` so that when executed it logs somewhere
what line is being visited. Finally we execute the instrumented version of
`aha` and collect the desired information from the log.

More generally speaking, and especially within the CPROVER code base,
instrumenting the code often refers to modify its behavior in a manner that
makes it easier for a given analysis to do its job, regardless of whether that
is achieved by executing the instrumented code or by just analyzing it in some
other way.

\subsection flattening_lowering_subsection Flattening and Lowering

As we have seen above, we often operate on many different representations
of programs, such as ASTs, control flow graphs, SSA programs, logical formulas
in BMC and so on. Each of these forms is good for certain kinds of analyses,
transformations or optimizations.

One important kind of step in dealing with program representations is
going from one representation to the other. Often, such steps are going
from a more ''high-level'' representation (closer to the source code)
to a more ''low-level'' representation. Such transformation steps are
known as **flattening** or **lowering** steps, and tend to be more-or-less
irreversible.

An example of a lowering step is the transformation from ASTs to the GOTO IR,
given above. 

\subsection verification_condition_subsection Verification Condition

In the CPROVER framework, the term **verification condition** is used
in a somewhat non-standard way. Let a program and a set of assertions
be given. We transform the program into an (acyclic) SSA (i.e., an SSA
with all loops unrolled a finite number of times) and turn it into a
logical formula, as described above. Note that in this case, the
formula will also contain information about what the program does
after the assertion is reached: this part of the formula, is, in fact,
irrelevant for deciding whether the program can satisfy the assertion or
not. The *verification condition* is the part of the formula that only
covers the program execution until the line that checks the assertion
has been executed, with everything that comes after it removed.


