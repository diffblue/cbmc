\ingroup module_hidden
\defgroup goto-instrument goto-instrument

# Folder goto-instrument

\author Martin Brain

The `goto-instrument/` directory contains a number of tools, one per
file, that are built into the `goto-instrument` program. All of them
take in a goto-program (produced by `goto-cc`) and either modify it or
perform some analysis. Examples include `nondet_static.cpp` which
initialises static variables to a non-deterministic value,
`nondet_volatile.cpp` which assigns a non-deterministic value to any
volatile variable before it is read and `weak_memory.h` which performs
the necessary transformations to reason about weak memory models. The
exception to the “one file for each piece of functionality” rule are the
program instrumentation options (mostly those given as “Safety checks”
in the `goto-instrument` help text) which are included in the
`goto-program/` directory. An example of this is
`goto-program/stack_depth.h` and the general rule seems to be that
transformations and instrumentation that `cbmc` uses should be in
`goto-program/`, others should be in `goto-instrument`.

`goto-instrument` is a very good template for new analysis tools. New
developers are advised to copy the directory, remove all files apart
from `main.*`, `parseoptions.*` and the `Makefile` and use these as the
skeleton of their application. The `doit()` method in `parseoptions.cpp`
is the preferred location for the top level control for the program.

### Main usage ###

For most of the transformations, `goto-instrument` takes one or two 
arguments and any number of options. The two file arguments are 
a goto-binary that it uses
as an input for the transformation, and then *another goto binary* that
it uses to write the result of the transformation. This is important
because many times, if you don't supply a second filename for the 
goto-binary to be written to, you get the equivalent of the `--help`
option output, with no indication of what has gone wrong. Some of the options
can work with just an input file and not output file. For more specific
examples, take a look at the demonstrations below:

### Function pointer removal ###

As an example of a transformation pass being run, imagine you have a file 
called `function_pointers.c` with the following content:

	int f1(void);
	int f2(void);
	int f3(void);
	int f4(void);

	int (* const fptbl1[][2])(void) = {
	  { f1, f2 },
	  { f3, f4 },
	};

	int g1(void);
	int g2(void);

	int (* const fptbl2[])(void) = {
	  g1, g2
	};

	int func(int id1, int id2)
	{
	  int t;
	  t = fptbl1[id1][id2]();
	  t = fptbl2[id1]();
	  return t;
	}

Then, assuming you have compiled it to a goto-binary with `goto-cc`, called 
`function_pointers.goto`, you could see the output of the 
`--show-goto-functions` flag on the unmodified program:

	Reading GOTO program from `function_pointers.goto'
	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

	func /* func */
	        // 0 file function_pointer.c line 20 function func
	        signed int t;
	        // 1 file function_pointer.c line 21 function func
	        t=fptbl1[(signed long int)id1][(signed long int)id2]();
	        // 2 file function_pointer.c line 22 function func
	        t=fptbl2[(signed long int)id1]();
	        // 3 file function_pointer.c line 23 function func
	        return t;
	        // 4 file function_pointer.c line 23 function func
	        dead t;
	        // 5 file function_pointer.c line 23 function func
	        GOTO 1
	        // 6 file function_pointer.c line 24 function func
	     1: END_FUNCTION


Then, you can run a transformation pass with `goto-instrument --remove-function-pointers function_pointers.goto function_pointers_modified.goto`, 
and then ask to show the result of the transformation through
showing the goto-functions again:

	Reading GOTO program from `function_pointers_modified.goto'
	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

	func /* func */
	        // 0 file function_pointer.c line 20 function func
	        signed int t;
	        // 1 file function_pointer.c line 21 function func
	        fptbl1[(signed long int)id1][(signed long int)id2];
	        // 2 file function_pointer.c line 21 function func
	        IF fptbl1[(signed long int)id1][(signed long int)id2] == f3 THEN GOTO 1
	        // 3 file function_pointer.c line 21 function func
	        IF fptbl1[(signed long int)id1][(signed long int)id2] == f2 THEN GOTO 2
	        // 4 file function_pointer.c line 21 function func
	        IF fptbl1[(signed long int)id1][(signed long int)id2] == f1 THEN GOTO 3
	        // 5 file function_pointer.c line 21 function func
	        IF fptbl1[(signed long int)id1][(signed long int)id2] == f4 THEN GOTO 4
	        // 6 file function_pointer.c line 21 function func
	        IF fptbl1[(signed long int)id1][(signed long int)id2] == g1 THEN GOTO 5
	        // 7 file function_pointer.c line 21 function func
	        IF fptbl1[(signed long int)id1][(signed long int)id2] == g2 THEN GOTO 6
	        // 8 file function_pointer.c line 21 function func
	     1: t=f3();
	        // 9 file function_pointer.c line 21 function func
	        GOTO 7
	        // 10 file function_pointer.c line 21 function func
	     2: t=f2();
	        // 11 file function_pointer.c line 21 function func
	        GOTO 7
	        // 12 file function_pointer.c line 21 function func
	     3: t=f1();
	        // 13 file function_pointer.c line 21 function func
	        GOTO 7
	        // 14 file function_pointer.c line 21 function func
	     4: t=f4();
	        // 15 file function_pointer.c line 21 function func
	        GOTO 7
	        // 16 file function_pointer.c line 21 function func
	     5: t=g1();
	        // 17 file function_pointer.c line 21 function func
	        GOTO 7
	        // 18 file function_pointer.c line 21 function func
	     6: t=g2();
	        // 19 file function_pointer.c line 22 function func
	     7: fptbl2[(signed long int)id1];
	        // 20 file function_pointer.c line 22 function func
	        IF fptbl2[(signed long int)id1] == g1 THEN GOTO 8
	        // 21 file function_pointer.c line 22 function func
	        IF fptbl2[(signed long int)id1] == g2 THEN GOTO 9
	        // 22 file function_pointer.c line 22 function func
	     8: t=g1();
	        // 23 file function_pointer.c line 22 function func
	        GOTO 10
	        // 24 file function_pointer.c line 22 function func
	     9: t=g2();
	        // 25 file function_pointer.c line 23 function func
	    10: return t;
	        // 26 file function_pointer.c line 23 function func
	        dead t;
	        // 27 file function_pointer.c line 24 function func
	        END_FUNCTION

You can now see that the function pointer (indirect) call (resulting from 
the array indexing of the array containing the function pointers) 
has now been substituted by direct, conditional calls.

### Call Graph ###

This is an example of a command line flag that requires only one argument,
specifying the input file.

You can see the call graph of a particular goto-binary by issuing `goto-instrument --call-graph <goto_binary>`. This gives a result similar to this:

	Reading GOTO program from `a.out'
	Function Pointer Removal
	Virtual function removal
	Cleaning inline assembler statements
	main -> fun
	__CPROVER__start -> __CPROVER_initialize
	__CPROVER__start -> main
	fun -> malloc

The interesting part of the output in the above text is the last four lines,
that show that `main` is calling `fun`, `__CPROVER__start` is calling `__CPROVER_initialize` and `main` and that `fun` is calling `malloc`. 
