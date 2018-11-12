\ingroup module_hidden
\page other_documentation Other Documentation

\section satabs SATABS

We document two programs that try to achieve formal guarantees of the
absence of specific problems: CBMC and SATABS. The algorithms
implemented by CBMC and SATABS are complementary, and often, one tool is
able to solve a problem that the other cannot solve.

Both CBMC and SATABS are verification tools for ANSI-C/C++ programs.
They verify array bounds (buffer overflows), pointer safety, exceptions
and user-specified assertions. Both tools model integer arithmetic
accurately, and are able to reason about machine-level artifacts such as
integer overflow. CBMC and SATABS are therefore able to detect a class
of bugs that has so far gone unnoticed by many other verification tools.
This manual also covers some variants of CBMC, which includes HW-CBMC
for
[hardware/software co-verification](http://www.cprover.org/cprover-manual/hwsw.html).

## Automatic Program Verification with SATABS

In many cases, lightweight properties such as array bounds do not rely
on the entire program. A large fraction of the program is *irrelevant*
to the property. SATABS exploits this observation and computes an
*abstraction* of the program in order to handle large amounts of code.

In order to use SATABS it is not necessary to understand the abstraction
refinement process. For the interested reader, a high-level introduction
to abstraction refinement is provided
\ref man_satabs-overview "here".
We also provide
\ref man_satabs-tutorials "tutorials on how to use SATABS".

Just as CBMC, SATABS attempts to build counterexamples that refute the
property. If such a counterexample is found, it is presented to the
engineer to facilitate localization and repair of the program.

\subsection man_install-satabs Installing SATABS

### Requirements

SATABS is available for Windows, i86 Linux, and MacOS X. SATABS requires
a code pre-processing environment including a suitable preprocessor
and a set of header files.

1.  **Linux:** the preprocessor and the header files typically come with
    a package called *gcc*, which must be installed prior to the
    installation of SATABS.
2.  **Windows:** The Windows version of SATABS requires the preprocessor
    `cl.exe`, which is part of Visual Studio (including the free [Visual
    Studio
    Express](http://msdn.microsoft.com/vstudio/express/visualc/)).
3.  **MacOS:** Install Xcode command line tools: run
    `xcode-select --install`  prior to installing SATABS.

Important note for Windows users: Visual Studio's `cl.exe` relies on a
complex set of environment variables to identify the target architecture
and the directories that contain the header files. You must run SATABS
from within the *Visual Studio Command Prompt*.

Note that the distribution files for the [Eclipse
plugin](installation-plugin.shtml) include the command-line tools.
Therefore, if you intend to run SATABS exclusively within Eclipse, you
can skip the installation of the command-line tools. However, you still
have to install the compiler environment as described above.

### Choosing and Installing a Model Checker

You need to install a Model Checker in order to be able to run SATABS.
You can choose between following alternatives:

-   **Cadence SMV**. Available from http://www.kenmcmil.com/smv.html.
    Cadence SMV is a commercial model checker. The free version that is
    available on the homepage above must not be used for commercial
    purposes (read the license agreement thoroughly before you download
    the tool). The documentation for SMV can be found in the directory
    where you unzip/untar SMV under ./smv/doc/smv/. Read the
    installation instructions carefully. The Linux/MacOS versions
    require setting environment variables. You must add add the
    directory containing the `smv` binary (located in ./smv/bin/,
    relative to the path where you unpacked it) to your `PATH`
    environment variable. SATABS uses Cadence SMV by default.

-   **NuSMV**. Available from http://nusmv.irst.itc.it/. NuSMV is the
    open source alternative to Cadence SMV. Installation instructions
    and documentation can be found on the NuSMV homepage. The directory
    containing the NuSMV binary should be added to your `PATH`
    environment variable. Use the option

        --modelchecker nusmv

    to instruct SATABS to use NuSMV.

-   **BOPPO**. Available from http://www.cprover.org/boppo/. BOPPO is
    a model checker which uses SAT-solving algorithms. BOPPO relies on a
    built-in SAT solver and Quantor, a solver for quantified boolean
    formulas which is currently bundled with BOPPO, but also available
    separately from <http://fmv.jku.at/quantor/>. We recommend to add
    the directories containing both tools to your `PATH` environment
    variable. Use the option

        --modelchecker boppo

    when you call SATABS and want it to use BOPPO instead of SMV.

-   **BOOM**. Available from http://www.cprover.org/boom/. Boom has a
    number of unique features, including the verification of programs
    with unbounded thread creation.

### Installing SATABS

1.  Download SATABS for your operating system. The binaries are
    available from <http://www.cprover.org/satabs/>.
2.  Unzip/untar the archive into a directory of your choice. We
    recommend to add this directory to your `PATH` environment variable.

Now you can execute SATABS. Try running SATABS on the small examples
presented in the \ref man_satabs-tutorials "SATABS tutorial". If you use
the Cadence SMV model checker, the only command line arguments you have
to specify are the names of the files that contain your program.

### Requirements

We provide a graphical user interface to CBMC and SATABS, which is
realized as a plugin to the Eclipse framework. Eclipse is available at
http://www.eclipse.org. We do not provide installation instructions for
Eclipse (basically, you only have to download the current version and
extract the files to your hard-disk) and assume that you have already
installed the current version.

CBMC and SATABS have their own requirements. As an example, both CBMC
and SATABS require a suitable preprocessor and a set of header files.
As first step, you should therefore follow the installation instructions
for [CBMC](http://www.cprover.org/cprover-manual/installation-cbmc.html)
and [SATABS](http://www.cprover.org/cprover-manual/installation-satabs.html).

Important note for Windows users: Visual Studio's `cl.exe` relies on a
complex set of environment variables to identify the target architecture
and the directories that contain the header files. You must run Eclipse
from within the *Visual Studio Command Prompt*.

\section man_satabs SATABS---Predicate Abstraction with SAT

\subsection man_satabs-overview Overview

This section describes SATABS from the point of view of the user. To
learn about the technology implemented in SATABS, read
\ref man_satabs-background "this".

We assume you have already installed SATABS and the necessary support
files on your system. If not so, please follow
\ref man_install-satabs "these instructions".

While users of SATABS almost never have to be concerned about the
underlying refinement abstraction algorithms, understanding the classes
of properties that can be verified is crucial. Predicate abstraction is
most effective when applied to *control-flow dominated properties*. As
an example, reconsider the following program (lock-example-fixed.c):

```
    _Bool nondet_bool();
    _Bool LOCK = 0;

    _Bool lock() {
      if(nondet_bool()) {
        assert(!LOCK);
        LOCK=1;
        return 1; }

      return 0;
    }

    void unlock() {
      assert(LOCK);
      LOCK=0;
    }

    int main() {
      unsigned got_lock = 0;
      int times;

      while(times > 0) {
        if(lock()) {
          got_lock++;
          /* critical section */
        }

        if(got_lock!=0) {
          unlock();
          got_lock--;
        }

        times--;
      }
    }
```

The two assertions in the program model that the functions `lock()` and
`unlock()` are called in the right order. Note that the value of `times`
is chosen non-deterministically and is not bounded. The program has no
run-time bound, and thus, unwinding the code with CBMC will never
terminate.

### Working with Claims

The two assertions will give rise to two *properties*. Each property is
associated to a specific line of code, i.e., a property is violated when
some condition can become false at the corresponding program location.
SATABS will generate a list of all properties for the programs as
follows:

    satabs lock-example-fixed.c --show-properties

SATABS will list two properties; each property corresponds to one of the
two assertions. We can use SATABS to verify both properties as follows:

    satabs lock-example-fixed.c

SATABS will conclude the verification successfully, that is, both
assertions hold for execution traces of any length.

By default, SATABS attempts to verify all properties at once. A single
property can be verified (or refuted) by using the `--property id`
option of SATABS, where `id` denotes the identifier of the property in
the list obtained by calling SATABS with the `--show-properties` flag.
Whenever a property is violated, SATABS reports a feasible path that
leads to a state in which the condition that corresponds to the violated
property evaluates to false.

\subsection man_satabs-libraries Programs that use Libraries

SATABS cannot check programs that use functions that are only available
in binary (compiled) form (this restriction is not imposed by the
verification algorithms that are used by SATABS – they also work on
assembly code). The reason is simply that so far no assembly language
frontend is available for SATABS. At the moment, (library) functions for
which no C source code is available have to be replaced by stubs. The
usage of stubs and harnesses (as known from unit testing) also allows to
check more complicated properties (like, for example, whether function
`fopen` is always called before `fclose`). This technique is explained
in detail in the \ref man_satabs-tutorials "SATABS tutorials".

\subsection man_satabs-unit-test Unit Testing with SATABS

The example presented \ref man_satabs-tutorial-driver "here" is
obviously a toy example and can hardly be used to convince your project
manager to use static verification in your next project. Even though we
recommend to use formal verification and specification already in the
early phases of your project, the sad truth is that in most projects
verification (of any kind) is still pushed to the very end of the
development cycle.  Therefore, this section is dedicated to the
verification of legacy code.  However, the techniques presented here can
also be used for *unit testing*.

Unit testing is used in most software development projects, and static
verification with SATABS can be very well combined with this technique.
Unit testing relies on a number test cases that yield the desired code
coverage. Such test cases are implemented by a software testing engineer
in terms of a test harness (aka test driver) and a set of function
stubs. Typically, a slight modification to the test harness allows it to
be used with SATABS. Replacing the explicit input values with
non-deterministic inputs (as explained in
\ref man_satabs-tutorial-aeon "here" and
\ref man_satabs-tutorial-driver "here")) guarantees that SATABS will try
to achieve **full** path and state coverage (due to the fact that
predicate abstraction implicitly detects equivalence classes). However,
it is not guaranteed that SATABS terminates in all cases. Keep in mind
that you must not make any assumptions about the validity of the
properties if SATABS did not run to completion!

### Further Reading

-   [Model Checking Concurrent Linux Device
    Drivers](http://www.kroening.com/publications/view-publications-wbwk2007.html)
-   [SATABS: SAT-based Predicate Abstraction for
    ANSI-C](http://www-2.cs.cmu.edu/~svc/papers/view-publications-cksy2005.html)
-   [Predicate Abstraction of ANSI-C Programs using
    SAT](http://www-2.cs.cmu.edu/~svc/papers/view-publications-cksy2004.html)

\subsection man_satabs-background Background

### Sound Abstractions

This section provides background information on how SATABS operates.
Even for very trivial C programs it is impossible to exhaustively
examine their state space (which is potentially unbounded). However, not
all details in a C program necessarily contribute to a bug, so it may be
sufficient to only examine those parts of the program that are somehow
related to a bug.

In practice, many static verification tools (such as `lint`) try to
achieve this goal by applying heuristics. This approach comes at a cost:
bugs might be overlooked because the heuristics do not cover all
relevant aspects of the program. Therefore, the conclusion that a
program is correct whenever such a static verification tool is unable to
find an error is invalid.

\image html cegar-1.png "CEGAR Loop"

A more sophisticated approach that has been very successful recently is
to generate a *sound* abstraction of the original program. In this
context, *soundness* refers to the fact that the abstract program
contains (at least) all relevant behaviors (i.e., bugs) that are present
in the original program. In the Figure above, the first component strips
details from the original program. The number of possible behaviors
increases as the number of details in the abstract program decreases.
Intuitively, the reason is that whenever the model checking tool lacks
the information that is necessary to make an accurate decision on
whether a branch of an control flow statement can be taken or not, both
branches have to be considered.

In the resulting *abstract program*, a set of concrete states is
subsumed by means of a single abstract state. Consider the following
figure:

![](states.png)

The concrete states *x*~1~ and *x*~2~ are mapped to an abstract state
*X*, and similarly *Y* subsumes *y*~1~ and *y*~2~. However, all
transitions that are possible in the concrete program are also possible
in the abstract model. The abstract transition *X* → *Y* summarizes the
concrete transitions *x*~1~ → *y*~1~ and *x*~1~ → *x*~1~, and *Y* → *X*
corresponds to *x*~1~ → *x*~2~. The behavior *X* → *Y* → *X* is feasible
in the original program, because it maps to *x*~1~ → *x*~1~ → *x*~2~.
However, *Y* → *X* → *Y* is feasible only in the abstract model.

### Spurious Counterexamples

The consequence is that the model checker (component number two in the
figure above) possibly reports a *spurious* counterexample. We call a
counterexample spurious whenever it is feasible in the current abstract
model but not in the original program. However, whenever the model
checker is unable to find an execution trace that violates the given
property, we can conclude that there is no such trace in the original
program, either.

The feasibility of counterexamples is checked by *symbolic simulation*
(performed by component three in the figure above). If the
counterexample is indeed feasible, SATABS found a bug in the original
program and reports it to the user.

### Automatic Refinement

On the other hand, infeasible counterexamples (that originate from
abstract behaviors that result from the omission of details and are not
present in the original program) are never reported to the user.
Instead, the information is used in order to refine the abstraction such
that the spurious counterexample is not part of the refined model
anymore. For instance, the reason for the infeasibility of *Y* → *X* →
*Y* is that neither *y*~1~ nor *x*~1~ can be reached from *x*~2~.
Therefore, the abstraction can be refined by partitioning *X*.

The refinement steps can be illustrated as follows:

![Iterative refinement](refinement.png)

The first step (1) is to generate a very coarse abstraction with a very
small state space. This abstraction is then successively refined (2, 3,
...) until either a feasible counterexample is found or the abstract
program is detailed enough to show that there is no path that leads to a
violation of the given property. The problem is that this point is not
necessarily reached for every input program, i.e., it is possible that
the the abstraction refinement loop never terminates. Therefore, SATABS
allows to specify an upper bound for the number of iterations.

When this upper bound is reached and no counterexample was found, this
does not necessarily mean that there is none. In this case, you cannot
make any conclusions at all with respect to the correctness of the input
program.

\subsection man_satabs-tutorials Tutorials

We provide an introduction to model checking "real" C programs with
SATABS using two small examples.

\subsubsection man_satabs-tutorial-driver Reference Counting in Linux Device Drivers

Microsoft's [SLAM](http://research.microsoft.com/SLAM) toolkit has been
successfully used to find bugs in Windows device drivers. SLAM
automatically verifies device driver whether a device driver adheres to
a set of specifications. SLAM provides a test harness for device drivers
that calls the device driver dispatch routines in a non-deterministic
order. Therefore, the Model Checker examines all combinations of calls.
Motivated by the success this approach, we provide a toy example based
on Linux device drivers. For a more complete approach to the
verification of Linux device drivers, consider
[DDVerify](http://www.cprover.org/ddverify/).

Dynamically loadable modules enable the Linux Kernel to load device
drivers on demand and to release them when they are not needed anymore.
When a device driver is registered, the kernel provides a major number
that is used to uniquely identify the device driver. The corresponding
device can be accessed through special files in the filesystem; by
convention, they are located in the `/dev` directory. If a process
accesses a device file the kernel calls the corresponding `open`, `read`
and `write` functions of the device driver. Since a driver must not be
released by the kernel as long as it is used by at least one process,
the device driver must maintain a usage counter (in more recent Linux
kernels, this is done automatically, however, drivers that must maintain
backward compatibility have to adjust this counter).

We provide a skeleton of such a driver. Download the files
assets/spec.c, assets/driver.c, assets/driver.h, assets/kdev_t.h, and
assets/modules.h.

The driver contains following functions:

1.  `register_chrdev`: (in assets/spec.c) Registers a character device.
    In our implementation, the function sets the variable `usecount` to
    zero and returns a major number for this device (a constant, if the
    user provides 0 as argument for the major number, and the value
    specified by the user otherwise).

        int usecount;

        int register_chrdev (unsigned int major, const char* name)
        {
          usecount = 0;
          if (major == 0)
            return MAJOR_NUMBER;
          return major;
        }

2.  `unregister_chrdev`: (in assets/spec.c) Unregisters a character
    device.  This function asserts that the device is not used by any
    process anymore (we use the macro `MOD_IN_USE` to check this).

        int unregister_chrdev (unsigned int major, const char* name)
        {
          if (MOD_IN_USE)
            {
            ERROR: assert (0);
            }
          else
            return 0;
        }

3.  `dummy_open`: (in assets/driver.c) This function increases the
    `usecount`. If the device is locked by some other process
    `dummy_open` returns -1. Otherwise it locks the device for the
    caller.

4.  `dummy_read`: (in assets/driver.c) This function "simulates" a read
    access to the device. In fact it does nothing, since we are
    currently not interested in the potential buffer overflow that may
    result from a call to this function. Note the usage of the function
    `nondet_int`: This is an internal SATABS-function that
    non­determi­nistically returns an arbitrary integer value. The
    function `__CPROVER_assume` tells SATABS to ignore all traces that
    do not adhere to the given assumption. Therefore, whenever the lock
    is held, `dummy_read` will return a value between 0 and `max`. If
    the lock is not held, then `dummy_read` returns -1.

5.  `dummy_release`: (in assets/driver.c) If the lock is held, then
    `dummy_release` decreases the `usecount`, releases the lock, and
    returns 0. Otherwise, the function returns -1.

We now want to check if any *valid* sequence of calls of the dispatch
functions (in driver.c) can lead to the violation of the assertion (in
assets/spec.c). Obviously, a call to `dummy_open` that is immediately
followed by a call to `unregister_chrdev` violates the assertion.

The function `main` in spec.c gives an example of how these functions
are called. First, a character device "`dummy`" is registered. The major
number is stored in the `inode` structure of the device. The values for
the file structure are assigned non-deterministically. We rule out
invalid sequences of calls by ensuring that no device is unregistered
while it is still locked. We use the following model checking harness
for calling the dispatching functions:

```
    random = nondet_uchar ();
    __CPROVER_assume (0 <= random && random <= 3);

    switch (random)
    {
    case 1:
      rval = dummy_open (&inode, &my_file);
      if (rval == 0)
        lock_held = TRUE;
      break;
    case 2:
      __CPROVER_assume (lock_held);
      count = dummy_read (&my_file, buffer, BUF_SIZE);
      break;
    case 3:
      dummy_release (&inode, &my_file);
      lock_held = FALSE;
      break;
    default:
      break;
    }
```

The variable `random` is assigned non-deterministically. Subsequently,
the value of `random` is restricted to be 0 ≤ `random` ≤ 3 by a call
to `__CPROVER_assume`. Whenever the value of `random` is not in this
interval, the corresponding execution trace is simply discarded by
SATABS. Depending on the value of `random`, the harness calls either
`dummy_open`, `dummy_read` or `dummy_close`. Therefore, if there is a
sequence of calls to these three functions that leads to a violation of
the assertion in `unregister_chrdev`, then SATABS will eventually
consider it.

If we ask SATABS to show us the properties it verifies with

    satabs driver.c spec.c --show-properties

for our example, we obtain

1.  Claim unregister\_chrdev.1:\
        file spec.c line 18 function unregister\_chrdev\
        MOD\_IN\_USE in unregister\_chrdev\
        FALSE

2.  Claim dummy\_open.1:\
        file driver.c line 15 function dummy\_open\
        i\_rdev mismatch\
        (unsigned int)inode-&gt;i\_rdev &gt;&gt; 8 == (unsigned
    int)dummy\_major

It seems obvious that the property dummy\_open.1 can never be violated.
SATABS confirms this assumption: We call

    satabs driver.c spec.c --property dummy_open.1

and SATABS reports `VERIFICATION SUCCESSFUL` after a few iterations.

If we try to verify property unregister\_chrdev.1, SATABS reports that
the property in line 18 in file spec.c is violated (i.e., the assertion
does not hold, therefore the `VERIFICATION FAILED`). Furthermore, SATABS
provides a detailed description of the problem in the form of a
counterexample (i.e., an execution trace that violates the property). On
this trace, `dummy_open` is called **twice**, leading to a `usecount` of 2.
The second call of course fails with `rval=-1`, but the counter is
increased nevertheless:

```
    int dummy_open (struct inode *inode, struct file *filp)
    {
      __CPROVER_assert(MAJOR (inode->i_rdev) == dummy_major,
          "i_rdev mismatch");
      MOD_INC_USE_COUNT;

      if (locked)
        return -1;
      locked = TRUE;

      return 0; /* success */
    }
  ```

Then, `dummy_release` is called to release the lock on the device.
Finally, the loop is left and the call to `unregister_chrdev` results in
a violation of the assertion (since `usecount` is still 1, even though
`locked=0`).

\subsubsection man_satabs-tutorial-aeon Buffer Overflow in a Mail Transfer Agent

We explain how to model check Aeon version 0.2a, a small mail transfer
agent written by Piotr Benetkiewicz. The description advertises Aeon as
a "*good choice for **hardened** or minimalistic boxes*". The sources
are available
[here](http://www.cprover.org/satabs/examples/loop_detection/aeon-0.2a.tar.gz).

Our first naive attempt to verify Aeon using

    satabs *.c

produces a positive result, but also warns us that the property holds
trivially. It also reveals that a large number library functions are
missing: SATABS is unable to find the source code for library functions
like `send`, `write` and `close`.

Now, do you have to provide a body for all missing library functions?
There is no easy answer to this question, but a viable answer would be
"most likely not". It is necessary to understand how SATABS handles
functions without bodies: It simply assumes that such a function returns
an arbitrary value, but that no other locations than the one on the left
hand side of the assignment are changed. Obviously, there are cases in
which this assumption is un­sound, since the function potentially
modifies all memory locations that it can somehow address.

We now use static analysis to generate array bounds checks for Aeon:

    satabs *.c --pointer-check --bounds-check --show-properties

SATABS will show about 300 properties in various functions (read
[this](http://www.cprover.org/cprover-manual/properties.html) for
more information on the property instrumentation).
Now consider the first few lines of the `main` function of Aeon:

    int main(int argc, char **argv)
    {
      char settings[MAX_SETTINGS][MAX_LEN];
      ...
      numSet = getConfig(settings);
      if (numSet == -1) {
        logEntry("Missing config file!");
        exit(1);
      }
      ...

and the function `getConfig` in `lib_aeon.c`:

    int getConfig(char settings[MAX_SETTINGS][MAX_LEN])
    {
        char home[MAX_LEN];
    FILE *fp;	/* .rc file handler */
    int numSet = 0;	/* number of settings */

    strcpy(home, getenv("HOME"));  	/* get home path */
    strcat(home, "/.aeonrc");	/* full path to rc file */
    fp = fopen(home, "r");
    if (fp == NULL) return -1;	/* no cfg - ERROR */
      while (fgets(settings[numSet], MAX_LEN-1, fp)
        && (numSet < MAX_SETTINGS)) numSet++;
    fclose(fp);

    return numSet;
    }

The function `getConfig` makes calls to `strcpy`, `strcat`, `getenv`,
`fopen`, `fgets`, and `fclose`. It is very easy to provide an
implementation for the functions from the string library (string.h), and
SATABS comes with meaningful definitions for most of them. The
definition of `getenv` is not so straight-forward. The man-page of
`getenv` (which we obtain by entering `man 3 getenv` in a Unix or cygwin
command prompt) tells us:

    `` `getenv' `` searches the list of en­vi­ron­ment variable names
    and values (using the global pointer `char **environ`) for a
    variable whose name matches the string at `NAME`. If a variable name
    matches, `getenv` returns a pointer to the associated value.

SATABS has no information whatsoever about the content of `environ`.
Even if SATABS could access the environment variables on your
computer, a successful verification of `Aeon` would then only guarantee
that the properties for this program hold on your computer with a
specific set of en­vi­ron­ment variables. We have to assume that
`environ` contains en­vi­ron­ment variables that have an arbitrary
content of arbitrary length. The content of en­vi­ron­ment variables is
not only arbitrary but could be malefic, since it can be modified by the
user. The approximation of the behavior of `getenv` that is shipped with
SATABS completely ignores the content of the string.

Now let us have another look at the properties that SATABS generates for
the models of the string library and for `getenv`. Most of these
properties require that we verify that the upper and lower bounds of
buffers or arrays are not violated. Let us look at one of the properties
that SATABS generates for the code in function `getConfig`:

    Claim getConfig.3:   file lib_aeon.c line 19 function getConfig   dereference failure: NULL plus offset pointer   !(SAME-OBJECT(src, NULL))`

The model of the function `strcpy` dereferences the pointer returned by
`getenv`, which may return a NULL pointer. This possibility is detected
by the static analysis, and thus a corresponding property is generated.
Let us check this specific property:

    satabs *.c --pointer-check --bounds-check --property getConfig.3

SATABS immediately returns a counterexample path that demonstrates how
`getenv` returns a NULL, which is subsequently dereferenced. We have
identified the first bug in this program: it requires that the
environment variable HOME is set, and crashes otherwise.

Let us examine one more property in the same function:

    Claim getConfig.7:   file lib_aeon.c line 19 function getConfig   dereference failure: array `home' upper bound   !(POINTER_OFFSET(dst) + (int)i >= 512) || !(SAME-OBJECT(dst, &home[0]))

This property asserts that the upper bound of the array `home` is not
violated. The variable `home` looks familiar: We encountered it in the
function `getConfig` given above. The function `getenv` in combination
with functions `strcpy`, `strcat` or `sprintf` is indeed often the
source for buffer overflows. Therefore, we try to use SATABS to check
the upper bound of the array `home`:

    satabs *.c --pointer-check --bounds-check --property getConfig.7

SATABS runs for quite a while and will eventually give up, telling us
that its upper bound for abstraction refinement iterations has been
exceeded. This is not exactly the result we were hoping for, and we
could now increase the bound for iterations with help of the
`--iterations` command line switch of SATABS.

Before we do this, let us investigate why SATABS has failed to provide a
useful result. The function `strcpy` contains a loop that counts from 1
to the length of the input string. Predicate abstraction, the mechanism
SATABS is based on, is unable to detect such loops and will therefore
unroll the loop body as often as necessary. The array `home` has
`MAX_LEN` elements, and `MAX_LEN` is defined to be 512 in `aeon.h`.
Therefore, SATABS would have to run through at least 512 iterations,
only to verify (or reject) one of the more than 300 properties! Does
this fact defeat the purpose of static verification?

We can make the job easier: after reducing the value of `MAX_LEN` in
`aeon.h` to a small value, say to 10, SATABS provides a counterexample
trace that demonstrates how the buffer overflow be reproduced. If you
use the Eclipse plugin (as described
[here](http://www.cprover.org/cprover-manual/installation-plugin.html)),
you can step through this counterexample. The trace contains the string
that is returned by `getenv`.
