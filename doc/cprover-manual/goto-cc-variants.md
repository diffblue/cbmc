[CPROVER Manual TOC](../)

## Variants of goto-cc

The goto-cc utility comes in several variants, summarised in the
following table.

Executable    | Environment                                                             | Preprocessor
--------------|-------------------------------------------------------------------------|-------
  goto-cc     | [gcc](http://gcc.gnu.org/) (control-flow graph only)                    | gcc -E
  goto-gcc    | [gcc](http://gcc.gnu.org/) ("hybrid" executable)                        | gcc -E
  goto-armcc  | [ARM RVDS](http://arm.com/products/tools/software-tools/rvds/index.php) | armcc -E
  goto-cl     | [Visual Studio](http://www.microsoft.com/visualstudio/)                 | cl /E
  goto-cw     | [Freescale CodeWarrior](http://www.freescale.com/webapp/sps/site/homepage.jsp?code=CW_HOME) | mwcceppc

The primary difference between the variants is the preprocessor called.
Furthermore, the language recognized varies slightly. The variants can
be obtained by simply renaming the goto-cc executable. On Linux/MacOS,
the variants can be obtained by creating a symbolic link.

The "hybrid" executables contain both the control-flow graph for
verification purposes and the usual, executable machine code.

