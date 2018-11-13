\ingroup module_hidden
\page jbmc-user-manual JBMC User Manual


\section jbmc-manual-intro Introduction

JBMC is a bounded model checking tool for the Java language. It follows the
same principles as CBMC, thus the existing
[documentation for CBMC](http://www.cprover.org/cprover-manual/cbmc.html)
largely applies to JBMC.

In brief, JBMC creates a model from Java Bytecode (given as input as a .class
file or a .jar) and performs static analysis and symbolic execution which allow
us to prove or refute properties. These properties are either automatically
generated (runtime errors), or provided by the user in the form of assertions.

Using examples, the following section will guide you through the basic
features of JBMC.


\section jbmc-tutorial JBMC tutorial

\subsection jbmc-manual-auto-assert Automatic assertions

Consider the following simplistic `ExampleArray.java` file which we have
compiled into `tutorial/ExampleArray.class` and which queries the array of
input arguments at index 3:
```
 1| package tutorial;
 2|
 3| public class ExampleArray {
 4|
 5|     public static void main(String[] args) {
 6|         final int index = 3;
 7|         String arg3 = args[index];
 8|     }
 9|
10| }
```

Now let's run the following command to let JBMC tell us about potential errors
in our program.

    $ jbmc tutorial/ExampleArray.class

The output contains the following:
```c
[java::tutorial.ExampleArray.main:([Ljava/lang/String;)V.null-pointer-exception.1] line 7 Null pointer check: SUCCESS
[java::tutorial.ExampleArray.main:([Ljava/lang/String;)V.array-index-out-of-bounds-low.1] line 7 Array index should be >= 0: SUCCESS
[java::tutorial.ExampleArray.main:([Ljava/lang/String;)V.array-index-out-of-bounds-high.1] line 7 Array index should be < length: FAILURE
[java::tutorial.ExampleArray.main:([Ljava/lang/String;)V.1] line 7 no uncaught exception: SUCCESS

** 1 of 13 failed (2 iterations)
VERIFICATION FAILED
```

We have a reported failure: JBMC found that the array access could potentially
be out of bounds, if the size of the argument array is too small.

If we make our code more robust by adding guards to make the array access
safe as follows:
```
  1| package tutorial;
  2|
  3| public class ExampleArraySafe {
  4|
  5|     public static void main(String[] args) {
  6|         final int index = 3;
  7|         String arg3 = "none";
  8|         if (index < args.length) {
  9|             arg3 = args[index];
 10|         }
 11|     }
 12|
 13| }
```
then when running JBMC on that corrected version:

    $ jbmc tutorial/ExampleArraySafe.class

all the automatic assertions become valid, meaning that there is no
possible inputs (argument values) for which they can be violated:
```c
[java::tutorial.ExampleArraySafe.main:([Ljava/lang/String;)V.1] line 7 no uncaught exception: SUCCESS
[java::tutorial.ExampleArraySafe.main:([Ljava/lang/String;)V.null-pointer-exception.1] line 8 Null pointer check: SUCCESS
[java::tutorial.ExampleArraySafe.main:([Ljava/lang/String;)V.null-pointer-exception.2] line 9 Null pointer check: SUCCESS
[java::tutorial.ExampleArraySafe.main:([Ljava/lang/String;)V.array-index-out-of-bounds-low.1] line 9 Array index should be >= 0: SUCCESS
[java::tutorial.ExampleArraySafe.main:([Ljava/lang/String;)V.array-index-out-of-bounds-high.1] line 9 Array index should be < length: SUCCESS
```

\subsection jbmc-manual-unwind Loop unwinding

As CBMC, JBMC needs to unwind loops up to a given value. Consider the `isPrime`
method in the code below. Without specifying an unwind limit, JBMC will not
terminate when analyzing the following function whose state representation is
theoretically unbounded (because of the for-loop whose number of iterations
depends on an input):
```
 1| package tutorial;
 2|
 3| public class ExampleUnwind {
 4|
 5|     public static void doSomething(int inputVal) {
 6|         if (inputVal > 1 && inputVal % 2 == 1) {
 7|             assert isPrime(inputVal);
 8|             // do something
 9|         }
10|     }
11|
12|     public static boolean isPrime(int candidate) {
13|         for (int div = 2; div * div <= candidate; div++) {
14|             if (candidate % div == 0) {
15|                 return false;
16|             }
17|         }
18|         return candidate > 1;
19|     }
20|
21| }
 ```
To limit the number of times the for-loop is unwound, we use the `--unwind N`
options, in which case the following call to JBMC:

    $ jbmc tutorial/ExampleUnwind.class --function tutorial.ExampleUnwind.isPrime --unwind 10

will terminate correctly. In this case, we will see `VERIFICATION SUCCESSFUL`,
as no automatic assertions are violated.

Note that in that example, there are is no main function, so we give specify
the desired entry point via the `--function` option.


\subsection jbmc-manual-user-assert User assertions

Elaborating on the example above, users may provide their own assertions, that
JBMC will try to refute. On line 7, we check the assertion that all odd
numbers greater than 1 are prime. To be sure that this always holds, we run
JBMC on the example, with a reasonable `unwind` value:

    $ jbmc tutorial/ExampleUnwind.class --function tutorial.ExampleUnwind.doSomething --unwind 10

Unsurprisingly JBMC doesn't agree, and prints an assertion failure
(truncated here for readability):
```c
[...doSomething:(I)V.assertion.1] line 7 assertion at file tutorial/ExampleUnwind.java: FAILURE
```

Rerunning the analysis with the `--trace` option, the following line appears
somewhere in the trace output and tells us which input value JBMC found to
trigger the violation (note that to see the original parameter names in the
trace output, the Java source must be compiled in debug mode: `javac -g`):
```c
INPUT inputVal: 15
```
The value chosen by JBMC is arbitrary, and could as well be 9
or 2084569161.

\subsection jbmc-manual-library Java Library support

The examples above only involve primitive types. In order to analyse code
involving Java Library classes, the core models (located in the same
repository) need to be added to the classpath:

    --cp <path_to_cbmc>/jbmc/src/java_bytecode/library/core-models.jar


The core models library simulate the behavior of the Java Library and
contains some commonly used classes, such as Object, Class, String, Enum.
Some JBMC-specific utilities reside in the `org.cprover` package.

Using the models, JBMC can reason with a variety of String operations
from `java.lang.String`, e.g.
```
  1| package tutorial;
  2|
  3| public class ExampleModels {
  4|
  5|     public static void main(String[] args) {
  6|         StringBuilder sb = new StringBuilder("abcd");
  7|         StringBuilder sb2 = sb.insert(2, "$");
  8|         assert sb2.toString().startsWith("abc");
  9|     }
 10|
 11| }
```
The following command line (note that the current directory is also added to
the classpath):

    $ jbmc tutorial/ExampleModels.class --cp <path_to_cbmc>/jbmc/src/java_bytecode/library/core-models.jar:.

will flag this violation (truncated):
```c
[java::tutorial.ExampleModels.stringOp:()V.assertion.1] line 8 assertion: FAILURE
```

Again, the trace (when re-running with `--trace`) shows the string violating
the condition in the assertion:
```c
dynamic_object2={ 'a', 'b', '$', 'c', 'd' }
```

\subsection jbmc-manual-exceptions Exceptions

In its analysis, JBMC can take into account exceptions thrown by user code or
library classes, as well as runtime exceptions such as NullPointerException.
To have JBMC reliably notify about all uncaught exceptions, the
`--throw-runtime-exceptions` can be used.

Consider the following code:
```
  1| package tutorial;
  2|
  3| public class ExampleExceptions {
  4|
  5|     public static int strLength(String str) {
  6|         return str.length();
  7|     }
  8|
  9| }
```

When given the `--throw-runtime-exceptions` options:

    $ jbmc tutorial/ExampleExceptions --tutorial.ExampleExceptions.strLength --throw-runtime-exceptions

JBMC will signal that the `str.length()` call may throw a runtime exception
and that this exception is not caught.

```c
[java::tutorial.ExampleExceptions.strLength:(Ljava/lang/String;)I.1] line 6 no uncaught exception: FAILURE
```
This could be fixed by adding a try-catch statement, or else checking that
`str` is non-null before accessing it.

To silence errors about uncaught exceptions while keeping JBMC's ability to
throw runtime exceptions (for example when analyzing code that has try-catch
blocks), the `--disable-uncaught-exception-check` option can be added.
In our example, the assertion check will disappear completely
from the output:
```
Generated 2 VCC(s), 0 remaining after simplification
VERIFICATION SUCCESSFUL
```

When analyzing this function without runtime exception support:

    $ jbmc tutorial/ExampleExceptions

JBMC only reports the error as a null pointer check failure:
```
[...null-pointer-exception.1] line 6 Null pointer check: FAILURE
[...strLength:(Ljava/lang/String;)I.1] line 6 no uncaught exception: SUCCESS
```

It is worth noting that in the JVM, `assert` actually throws an AssertionError
on violation. This behavior can be replicated in JBMC by using the
`--throw-assertion-error`. Violations of user assertions (if uncaught) would
then be reported like any other uncaught exception.


\subsection jbmc-manual-further-doc Further documentation

JBMC has a wealth of other options that can either constrain the model (to
cope with complexity issues), or output more relevant information. The list
of all available options is printed by running:

    $ jbmc --help

