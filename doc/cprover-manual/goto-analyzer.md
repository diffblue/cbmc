[CPROVER Manual TOC](../)

## Goto Analyzer

`goto-analyzer` is an abstract interpreter which uses the same
front-end and GOTO binary representation as CBMC.  It is built along
with CBMC, so [the installation instructions](../installation/) are
the same.

The key difference is that CBMC under-approximates the
behaviour of the program (execution traces that are too long or
require too many loop unwindings are not considered) while
`goto-analyzer` over-approximates the behaviour of the program.  CBMC
can determine if a property is A. true for a bounded number of
iterations or B. false and giving an error trace.  In contrast
`goto-analyzer` can determine if a property is A. true for all
iterations or B. possibly false.  In this sense, each tool has its own
strengths and weaknesses.

To use `goto-analyzer` you need to give options for:
* What [task](#task) to perform after the abstract interpreter has run.
* How to format the [output](#output).
* Which [abstract interpreter](#abstractinterpreter) is used.
* Which [domain](#domain) is used to describe the state of the program
at a point during execution.
* How the [history](#history) of the control flow of the program determines the
number of points of execution.
* The [storage](#storage) that links points of execution and domains.


### Quick Start

As the space of configuration options is quite large and their
interactions can sometimes be subtle and complex, here are some
possible sets of options for a few common tasks.

I want to see if I can verify anything with `goto-analyzer`:
```
goto-analyzer --verify --recursive-interprocedural --vsd --vsd-values intervals --vsd-struct every-field --vsd-arrays smash --vsd-pointers value-set program.c
```


I want to make a big effort to verify things:
```
goto-analyzer  --verify --three-way-merge --vsd --vsd-values set-of-constants --vsd-struct every-field --vsd-arrays up-to-n-elements --vsd-pointers value-set --loop-unwinding-and-branching 17 --one-domain-per-history program.c
```


I want to discharge obvious conditions and remove unreachable code:
```
goto-analyzer --simplify out.gb --three-way-merge --vsd 
```


I want to build a dependency graph:
```
goto-analyzer --show --dot depgraph.dot --dependence-graph-vs
```



### Task

`goto-analyzer` first runs the abstract interpreter until it reaches a
fix-point, then it will perform the task the user has chosen.

`--show`
: Displays a domain for every instruction in the GOTO binary.  The
format and information will depend on the [domain](#domain) that has
been selected.  If there are multiple domains corresponding to the
same location (see [history](#history) below) these will be merged
before they are displayed.

`--show-on-source`
: The source code of the program is displayed line-by-line with the
abstract domains corresponding to each location displayed between
them.  As the analysis is done at the level of instructions in the
GOTO binary, some domains may not be displayed.  Also if parts of the
GOTO binary have been generated or manipulated by other tools, these
may not be displayed as there is no corresponding source.
`--show-on-source` is the more user-friendly output, but `--show` gives
a better picture of exactly what is computed.

`--verify`
: Every property in the program is checked to see whether it is true
(it always holds), unreachable, false if it is reachable (due to the
over-approximate analysis, it is not clear if locations are reachable
or if it is an over-approximation, so this is the best that can be
achieved) or unknown.  If there are multiple points of execution that
reach the same location, each will be checked and the answers
combined, with unknown taking precedence.

`--simplify output_file.gb`
: Produces a new version of the GOTO binary in which the program has
been simplified using information from the abstract interpreter.  The
exact simplification will depend on the domain that is used but
typically this might be replacing any expression that has a constant
value.  If this makes instructions unreachable (for example if `GOTO`
can be shown to never be taken) they will be removed.  Removal can be
deactivated by passing `--no-simplify-slicing`.  In the ideal world
simplify would be idempotent (i.e. running it a second time would not
simplify anything more than the first).  However there are edge cases
which are difficult or prohibitively expensive to handle in the
domain which can result in a second (or more) runs giving
simplification.  Submitting bug reports for these is helpful but they
may not be viable to fix.

`--unreachable-instructions`
: Lists which instructions have a domain which is bottom
(i.e. unreachable).  If `--function` has been used to set the program
entry point then this can flag things like the `main` function as
unreachable.

`--unreachable-functions`
: Similar to the previous option but reports which functions are
definitely unreachable rather than just instructions.

`--reachable-functions`
: The negation of the previous option, reports which functions may be
reachable.  Note that because the analysis is over-approximate, it
is possible this will mark functions as reachable when a more precise
analysis (possibly using CBMC) will show that there are no execution
traces that reach them.



### Output

These options control how the result of the task is output.  The
default is text to the standard output.  In the case of tasks that
produce goto-programs (`--simplify` for example), the output options
only affect the logging and not the final form of the program.

`--text file_name`
: Writes the output as plain text to `file_name`.

`--json file_name`
: Writes the output as a JSON object to `file_name`.

`--xml file_name`
: Writes the output as XML to `file_name`.  This is similar but not
exactly the same as the XML that CBMC generates.

`--dot file_name`
: Writes the output in GraphViz's DOT format to `file_name`.  This is
only supported by some domains and tasks (for example
`--show --dependence-graph`).


### Abstract Interpreter

These options control which abstract interpreter is used and how
the analysis is performed.  In principle this can significantly change
the accuracy and performance of `goto-analyzer` but the current
options are reasonably similar.

If `--verbosity` is set above `8` the abstract interpreter will log what
it is doing.  This is intended to aid developers in understanding how
the algorithms work, where time is being spent, etc. but can be
generally quite instructive.

`--legacy-ait`
: This is the default option.  Abstract interpretation is performed
eagerly from the start of the program until fixed-point is reached.
Functions are analysed as needed and in the order of that they are
reached.  This option also fixes the History and Storage options to
their defaults.

`--legacy-concurrent`
: This extends `--legacy-ait` with very restricted and special purpose
handling of threads.  This needs the domain to have certain unusual
properties for it to give a correct answer.  At the time of writing
only `--dependence-graph` is compatible with it.

`--recursive-interprocedural`
: This extends `--legacy-ait` by allowing the History and Storage to
be configured.  As the name implies, function calls are handled by
recursion within the interpreter.  This is a good all-round choice and
will likely become the default at some point in the future.

`--three-way-merge`
: This extends `--recursive-interprocedural` by performing a
"modification aware" merge after function calls.  At the time of
writing only `--vsd` supports the necessary differential reasoning.
If you are using `--vsd` this is recommended as it is more accurate 
with little extra cost.


### Domain

One of the most important options; this controls how the possible
states at a given execution point are represented and manipulated.

`--constants`
: The default option, this stores one constant value per variable.
This means it is fast but will only find things that can be resolved
by constant propagation.  The domain has some handling of arrays but
limited support for pointers which means that in can potentially give
unsound behaviour.  `--vsd --vsd-values constants` is probably a
better choice for this kind of analysis.

`--intervals`
: A domain that stores an interval for each integer and float
variable.  At the time of writing not all operations are supported so
the results can be quite over-approximate at points.  It also has
limitations in the handling of pointers so can give unsound results.
`--vsd --vsd-values intervals` is probably a better choice for this
kind of analysis.

`--not-null`
: This domain is intended to find which pointers are not null.  Its
implementation is very limited and it is not recommended.

`--dependence-graph`
: Tracks data flow and information flow dependencies between
instructions and produces a graph.  This includes doing points-to
analysis and tracking reaching definitions (i.e. use-def chains).
This is one of the most extensive, correct and feature complete domains.

`--vsd`
: This is the Variable Sensitivity Domain (VSD).  It is a non-relational
domain that stores an abstract object for each live variable.  Which
kind of abstract objects are used depends on the type of the variable
and the run-time configuration.  This means that sensitivity of the
domain can be chosen -- for example, do you want to track every
element of an array independently, or just a few of them or simply
ignore arrays all together.  A set of options to configure VSD are
given below.  This domain is extensive and does not have any known
architectural limits on correctness.  As such it is a good choice for
many kinds of analysis.

`--dependence-graph-vs`
: This is a variant of the dependence graph domain that uses VSD to do
the foundational pointer and reaching definitions analysis.  This
means it can be configured using the VSD options and give more precise
analysis (for example, field aware) of the dependencies.


#### Configuration of the Variable Sensitivity Domain

VSD has a wide range of options that allow you to choose what kind of
abstract objects (and thus abstractions) are used to represent
variables of each type.

`--vsd-values`
: This controls the abstraction used for values, both `int` and
`float`.  The default option is `constants` which tracks if the
variable has a constant value.  This is fast but not very precise so
it may well be unable to prove very much.  `intervals` uses an
interval that contains all of the possible values the variable can
take.  It is more precise than `constants` in all cases but a bit
slower.  It is good for numerical code. `set-of-constants` uses a set
of up to 10 (currently fixed) constants.  This is more general than
using a single constant but can make analysis up to 10 times (or in
rare cases 100 times) slower.  It is good for control code with flags
and modes.

`--vsd-structs`
: This controls how structures are handled.  The default is `top-bottom`
which uses an abstract object with just two states (top and bottom).
In effect writes to structures are ignored and reads from them will
always return top (any value).  The other alternative is `every-field`
which stores an abstract object for each field.  Depending on how many
structures are live at any one time and how many fields they have this
may increase the amount of memory used by the analyser by a reasonable
amount.  But this means that the analysis will be "field-sensitive".

`--vsd-arrays`
: This controls how arrays are handled.  As with structures, the
default is `top-bottom` which effectively ignores writes to the array
and returns top on a read.  More precise than this is `smash` which
stores one abstract element for all of the values.  This is relatively
cheap but a lot more precise, particularly if used with `intervals` or
`set-of-constants`.  `up-to-n-elements` generalises `smash` by storing
abstract objects for the first `n` elements of each array (`n` defaults to
10 and can be controlled by `--vsd-array-max-elements`) and then
condensing all other elements down to a single abstract object.  This
allows reasonably fine-grained control over the amount of memory used and
can give much more precise results for small arrays. `every-element`
is the most precise, but most expensive option where an abstract
element is stored for every entry in the array.

`--vsd-pointers`
: This controls the handling of pointers.  The default, `top-bottom` effectively
ignores pointers, this is OK if they are just read (all reads return
top) but if they are written then there is the problem that we know
that a variable is changed but we know don't which one, so we have to set
the whole domain to top.  `constants` is somewhat misleadingly named as it
uses an abstract object that tracks a pointer to a single variable.
This includes the offset within the variable; a stack of field names
for structs and abstract objects for offsets in arrays.  Offsets are
tracked even if the abstract object for the variable itself does not
distinguish different fields or indexes.  `value-set` is the most
precise option; it stores a set of pointers to single variables as
described above.

`--vsd-unions`
: At the time of writing there is only one option for unions which is
`top-bottom`, discarding writes and returning top for all reads from a
variable of union type.

`--vsd-data-dependencies`
: Wraps each abstract object with a set of locations where the
variable was last modified.  The set is reset when the variable is
written and takes the union of the two sides' sets on merge.  This was
originally intended for `--dependence-graph-vs` but has proved useful
for `--vsd` as well.  This is not strictly necessary for
`--three-way-merge` as the mechanism it uses to work out which
variables have changed is independent of this option.

`--vsd-liveness`
: Wraps each abstract object with the location of the last assignment
or merge.  This is more basic and limited than
`--vsd-data-dependencies` and is intended to track SSA-like regions of
variable liveness.

`--vsd-flow-insensitive`
: This does not alter the abstract objects used or their
configuration.  It disables the reduction of the domain when a branch
is taken or an assumption is reached.  This normally gives a small
saving in time but at the cost of a large amount of precision.  This
is why the default is to do the reduction.  It can be useful for
debugging issues with the reduction.


### History

To over-approximate what a program does, it is necessary to consider
all of the paths of execution through the program.  As there are a
potentially infinite set of traces (and they can be potentially
infinitely long) it is necessary to merge some of them.  The common
approach (the "collecting abstraction") is to merge all paths that
reach the same instruction.  The abstract interpretation is then done
between instructions without thinking about execution paths.  This
ensures termination but means that it is not possible to distinguish
different call sites, loop iterations or paths through a program.

Note that `--legacy-ait`, the default abstract interpreter fixes the
history to `--ahistorical` so you will need to choose another abstract
interpreter to make use of these options.

The history options select the abstraction of execution traces to use:

`--ahistorical`
: This is the default and the coarsest abstraction.  No history
information is kept, so all traces that reach an instruction are
merged.  This is the collecting abstraction that is used in most
abstract interpreters.

`--call-stack n`
: This is an inter-procedural abstraction; it tracks the call stack and
only merges traces that reach the same location and have the same call
stack.  The effect of this is equivalent to inlining all functions and
then using `--ahistorical`.  In larger programs this can be very
expensive in terms of both time and memory but can give much more
accurate results.  Recursive functions create a challenge as the call
stack will be different each time.  To prevent non-termination, the
parameter `n` limits how many times a loop of recursive functions can
be called.  When `n` is reached all later ones will be merged.
Setting this to `0` will disable the limit.

`--loop-unwind n`
: This tracks the backwards jumps that are taken in the current
function.  Traces that reach the same location are merged if their
history of backjumps is the same.  At most `n` traces are kept for
each location, after that they are merged regardless of whether their
histories match. This gives a similar effect to unrolling the loops
`n` times and then using `--ahistorical`.  In the case of nested
loops, the behaviour can be a little different to unrolling as the
limit is the number of times a location is reached, so a loop with `x`
iterations containing a loop with `y` iterations will require `n = x*y`.
The time and memory taken by this option will rise (at worst) linearly
in terms of `n`.  If `n` is `0` then there is no limit.  Be warned
that if there are loops that can execute an unbounded number of
iterations or if the domain is not sufficiently precise to identify
the termination conditions then the analysis will not terminate.

`--branching n`
: This works in a similar way to `--loop-unwind` but tracking forwards
jumps (`if`, `switch`, `goto`, etc.) rather than backwards ones.  This
gives per-path analysis but limiting the number of times each location
is visited.  There is not a direct form of program transformation that
matches this but it is similar to the per-path analysis that symbolic
execution does.  The scalability and the risk of non-termination if
`n` is `0` remain the same.  Note that the goto-programs generated by
various language front-ends have a conditional forwards jump to exit the
loop if the condition fails at the start and an unconditional backwards
jump at the end.  This means that `--branching` can wind up
distinguishing different loop iterations -- "has not exited for the
last 3 iterations" rather than "has jumped back to the top 3 times".

`--loop-unwind-and-branching n`
: Again, this is similar to `--loop-unwind` but tracks both forwards
and backwards jumps.  This is only a very small amount more expensive than
`--branching` and is probably the best option for detailed analysis of
each function.




### Storage

The histories described above are used to keep track of where in the
computation needs to be explored.  The most precise option is to keep
one domain for every history but in some cases, to save memory and
time, it may be desirable to share domains between histories.  The
storage options allow this kind of sharing.

`--one-domain-per-location`
: This is the default option.  All histories that reach the same
location will use the same domain.  Setting this means that the
results of other histories will be similar to setting
`--ahistorical`.  One difference is how and when widening occurs.
`--one-domain-per-location --loop-unwind n` will wait until `n`
iterations of a loop have been completed and then will start to widen. 

`--one-domain-per-history`
: This is the best option to use if you are using a history other than
`--ahistorical`.  It stores one domain per history which can result in
a significant increase in the amount of memory used.



### Other Options

`goto-analyzer` supports a number of other options for the C/C++
frontend, the platform, displaying program representations and
instrumentation.  These all function exactly the same as CBMC does.

It also supports specific analyses which do not fit into the
configurable scheme above.  At the time of writing this is just
`--taint` which performs a configurable taint analysis.

