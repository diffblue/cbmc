
This tool is meant to help decompose CBMC proofs.
It does this by producing a control-flow graph that contains information about where CBMC may run into issues.

```
goto-instrument FILE.goto FLAGS
```

The recommended file to use is `FUNCTION_harness1.goto` which is produced from the common Makefile. If this is not available, use `goto-cc` to compile all relevant source files into a `.goto` file.


Relevant FLAGS

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
  Recommended to run for the reason that it simplifies that program.


  --omit-function-pointers
  Removes function pointer edges from the graph, which have a habit of producing visual clutter.


  --add-library
  Includes the CBMC library for functions like `malloc`, `free`, etc.


