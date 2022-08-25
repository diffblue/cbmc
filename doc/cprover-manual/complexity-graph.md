[CPROVER Manual TOC](../)

## Complexity Graph

This tool is meant to help decompose CBMC proofs.
It does this by producing a control-flow graph that contains information about where CBMC may run into issues.

```
goto-instrument FILE.goto FLAGS
```

The recommended file to use is `FUNCTION_harness1.goto` which is produced from the Makefile provided in the starter kit. If this is not available, use `goto-cc` to compile all relevant source files into a `.goto` file.
We recommend this file because it is produced before any program transformations are made, which can complicate the graph.

## Relevant FLAGS

  --show-complexity-graph FILE.dot
  instructs CBMC to write the graph to the .dot file
  This can be compiled to a PDF by using the command
  ```
  dot -Tpdf FILE.dot -o FILE.pdf
  ```


  --complexity-graph-roots FUNCTION-NAME
  Instructs CBMC to generate the graph spanned by this function. This flag can be passed multiple times and produces one graph spanned by all roots. If no roots are provided, all functions in the provided source files will be used.
  Typically this will be `FUNCTION_harness`.


  --remove-function-body FUNCTION-NAME
  Removes the body of a function, which has the effect of removing all outedges of that vertex from the graph.


  --omit-function FUNCTION-NAME
  Omits a function from the graph entirely. Useful for removing high-indegree sink nodes to reduce visual clutter.


  --constant-propagator
  Recommended to run for the reason that it simplifies the underlying program, and hence the graph.


  --omit-function-pointers
  Removes function pointer edges from the graph, which have a habit of producing visual clutter.


  --add-library
  Includes the CBMC library for functions like `malloc`, `free`, etc.

  --complexity-graph-global-scores
  Uses a more global notion of scoring, where the "global score" for a node is the number of paths to that node multiplied by the sum of the global scores of its children. 

The following flags can be used with the main CBMC executable
```
cbmc FILE.goto FLAGS
```

  --show-complexity-graph-with-symex FILE.dot
  Write the complexity graph with symbolic execution information to FILE.dot.


  --show-complexity-graph-with-solver FILE.dot
  Write the complexity graph with symbolic execution and solver formula information to FILE.dot.
  This flag requires the addition of `--write-solver-stats-to FILE.out` to obtain solver formula information.


  --complexity-graph-instructions
  When used with '--show-complexity-graph-with-symex' or '--show-complexity-graph-with-solver' displays the instructions of the program that have a high cost in symbolic execution and/or the solver formula.

## Reading the graph

### Node shapes

- Rectangluar nodes: normal functions
- Elliptical nodes: private functions
- Diamond nodes: functions with no body
- Arrow-shaped nodes: function pointers
- Pentagon: standard/CBMC library functions

### Node colors

The intensity of red coloring on a node is a display of its complexity relative to other nodes in the graph.

When using `--show-complexity-graph-with-symex` with `--complexity-graph-instructions`, intensity of pink on instructions shows the complexity of that instruction in symbolic execution, and intensity of yellow shows the complexity of that instruction in the creation of the solver formula.


## Sample interaction

Suppose we have a function `foobar` and we'd like to do a proof for it.
After creating a GOTO file `foobar_harness1.goto` with the starter kit or `goto-cc`, try the following

```
goto-instrument foobar_harness1.goto --show-complexity-graph graph.dot --complexity-graph-roots foobar
```
Followed by
```
dot -Tpdf graph.dot -o graph.pdf
```

This will display the call graph for foobar.
The first step is to take steps to clean the graph.

Likely, you can ignore function pointers at this point. See [this page](http://cprover.diffblue.com/md__home_travis_build_diffblue_cbmc_doc_architectural_restrict-function-pointer.html) for how to restrict function pointers - the information provided in the graph displays CBMC's sound overapproximation of what functions can be targets of which function pointers.

Additionally, there may be some high-indegree functions in the graph that don't appear to be useful and just complicate the graph.
Let's say one of those functions is `notuseful`.
We can then run a new command
```
goto-instrument foobar_harness1.goto --show-complexity-graph graph.dot --complexity-graph-roots foobar --complexity-graph-omit-function-pointers --complexity-graph-omit-function notuseful
```
Which should provide a cleaner graph to inspect.


When doing a proof, you should use information provided in the graph along with some domain knowledge about the codebase to decide where to decompose. See `doc/cprover-manual/contracts-functions.md` for a tutorial on proof decomposition using function contracts, which we refer to as abstracting a function.
It's good to abstract functions that are complex. In the case that there is a simple function `g` that calls a complex function `f`, it may be better to abstract `g` if the contract is easier to write.
A good way to approximate where a contract is easy to write is by how many memory locations a function can write to.

