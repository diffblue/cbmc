[CPROVER Manual TOC](../)

## Integration into Build Systems with goto-cc

Existing software projects usually do not come in a single source file
that may simply be passed to a model checker. They rather come in a
multitude of source files in different directories and refer to external
libraries and system-wide options. A *build system* then collects the
configuration options from the system and compiles the software
according to build rules.

The most prevalent build tool on Unix (-based) systems surely is the
`make` utility. This tool uses build rules given in a *Makefile* that
comes with the software sources. Running software verification tools on
projects like these is greatly simplified by a compiler that first
collects all the necessary models into a single model file.
[goto-cc](http://www.cprover.org/goto-cc/) is such a model file
extractor, which can seamlessly replace `gcc` and `cl.exe` in Makefiles.
The normal build system for the project may be used to build the
software, but the outcome will be a model file with suitable detail for
verification, as opposed to a flat executable program. Note that goto-cc
comes in different variants depending on the compilation environment.
These variants are described [here](goto-cc-variants.shtml).

### Example: Building wu-ftpd

This example assumes a Unix-like machine.

1.  Download the sources of wu-ftpd from
    [here](ftp://ftp.wu-ftpd.org/pub/wu-ftpd/wu-ftpd-current.tar.gz).

2.  Unpack the sources by running ` tar xfz wu-ftpd-current.tar.gz`

3.  Change to the source directory, by entering, e.g.,
    `cd wu-ftpd-2.6.2`

4.  Configure the project for verification by running

    `./configure YACC=byacc CC=goto-cc --host=none-none-none`

5.  Build the project by running `make`. This creates multiple model
    files in the `src` directory. Among them is a model for the main
    executable `ftpd`.

6.  Run a model-checker, e.g., CBMC, on the model file:

        `cbmc src/ftpd`

    CBMC automatically recognizes that the file is a goto binary.

### Important Notes

More elaborate build or configuration scripts often make use of features
of the compiler or the system library to detect configuration options
automatically, e.g., in a `configure` script. Replacing `gcc` by goto-cc
at this stage may confuse the script, or detect wrong options. For
example, missing library functions do not cause goto-cc to throw an
error (only to issue a warning). Because of this, configuration scripts
sometimes falsely assume the availability of a system function or
library.

In the case of this or similar problems, it is more advisable to
configure the project using the normal routine, and replacing the
compiler setting manually in the generated Makefiles, e.g., by replacing
lines like `CC=gcc` by `CC=goto-cc`.

A helpful command that accomplishes this task successfully for many
projects is the following:

```plaintext
for i in `find . -name Makefile`; do   sed -e 's/^\(\s*CC[ \t]*=\)\(.*$\)/\1goto-cc/g' -i $i done
```

Here are additional examples on how to use goto-cc:

-   \ref man_goto-cc-linux "Linux Kernel"
-   \ref man_goto-cc-apache "Apache HTTPD"

A description of how to integrate goto-cc into Microsoft's Visual Studio
is \ref man_instrumentation-vs "here".

### Linking Libraries

Some software projects come with their own libraries; also, the goal may
be to analyze a library by itself. For this purpose it is possible to
use goto-cc to link multiple model files into a library of model files.
An object file can then be linked against this model library. For this
purpose, goto-cc also features a linker mode.

To enable this linker mode, create a link to the goto-cc binary by the
name of goto-ld (Linux and Mac) or copy the goto-cc binary to
goto-link.exe (Windows). The goto-ld tool can now be used as a seamless
replacement for the `ld` tool present on most Unix (-based) systems and
for the `link` tool on Windows.

The default linker may need to be replaced by `goto-ld` or
`goto-link.exe` in the build script, which can be achieved in much the
same way as replacing the compiler.

## Architectural Settings

The behavior of a C/C++ program depends on a number of parameters that
are specific to the architecture the program was compiled for. The three
most important architectural parameters are:

-   The width of the various scalar types; e.g., compare the value of
    `sizeof(long int)` on various machines.
-   The width of pointers; e.g., compare the value of `sizeof(int *)` on
    various machines.
-   The [endianness](http://en.wikipedia.org/wiki/Endianness) of
    the architecture.

In general, the CPROVER tools attempt to adopt the settings of the
particular architecture the tool itself was compiled for. For example,
when running a 64 bit binary of CBMC on Linux, the program will be
processed assuming that `sizeof(long int)==8`.

As a consequence of these architectural parameters, you may observe
different verification results for an identical program when running
CBMC on different machines. In order to get consistent results, or when
aiming at validating a program written for a different platform, the
following command-line arguments can be passed to the CPROVER tools:

-   The word-width can be set with `--16`, `--32`, `--64`.
-   The endianness can be defined with `--little-endian` and
    `--big-endian`.

When using a goto binary, CBMC and the other tools read the
configuration from the binary, i.e., the setting when running goto-cc is
the one that matters; the option given to the model checker is ignored
in this case.

In order to see the effect of the options `--16`, `--32` and `--64`,
pass the following program to CBMC:

```C
#include <stdio.h>
#include <assert.h>

int main() {
  printf("sizeof(long int): %d\n", (int)sizeof(long int));
  printf("sizeof(int *): %d\n", (int)sizeof(int *));
  assert(0);
}
```

The counterexample trace contains the strings printed by the `printf`
command.

The effects of endianness are more subtle. Try the following program
with `--big-endian` and `--little-endian`:

```C
#include <stdio.h>
#include <assert.h>

int main() {
  int i=0x01020304;
  char *p=(char *)&i;
  printf("Bytes of i: %d, %d, %d, %d\n", p[0], p[1], p[2], p[3]);
  assert(0);
}
```

