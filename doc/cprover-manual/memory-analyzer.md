[CPROVER Manual TOC](../../)

## Memory Analyzer

The memory analyzer is a front-end for running and querying GDB in order to
obtain a state of the input program. The GDB is not needed to be executed
directly but is rather used as a back-end for the memory analysis. A common
application would be to obtain a snapshot of a program under analysis at a
particular state of execution. Such a snapshot could be useful on its own: to
query about values of particular variables. Furthermore, since that snapshot is
a state of a valid concrete execution, it can also be used for subsequent
analyses.

## Usage

We assume that the user wants to inspect a binary executable compiled with
debugging symbols and a symbol table information understandable by CBMC, e.g.
(having `goto-gcc` on the `PATH`):

```sh
$ goto-gcc -g input_program.c -o input_program_exe
```

Calling `goto-gcc` instead of simply compiling with `gcc` produces an ELF binary
with a goto section that contains the goto model (goto program + symbol table)
[goto-cc-variants](../goto-cc/variants/).

The memory analyzer supports two workflows to initiate the GDB with user code:
either to run the code from a core-file or up to a break-point. If the user
already has a core-file, they can specify it with the option `--core-file cf`.
If the user knows the point of their program from where they want to run the
analysis, they can specify it with the option `--breakpoint bp`. Only one of
core-file/break-point option can be used.

The tool also expects a comma-separated list of symbols to be analysed
`--symbols s1, s2, ..`. Given its dependence on GDB, `memory-analyzer` is a
Unix-only tool. The tool calls `gdb` to obtain the snapshot which is why the
`-g` option is necessary for the program symbols to be visible.

Take for example the following program:

```C
// main.c
void checkpoint() {}

int array[] = {1, 2, 3};

int main()
{
  array[1] = 4;

  checkpoint();

  return 0;
}
```

Say we are interested in the evaluation of `array` at the call-site of
`checkpoint`. We compile the program with

```sh
$ goto-gcc -g main.c -o main_exe
```

And then we call `memory-analyzer` with:

```sh
$ memory-analyzer --breakpoint checkpoint --symbols array main_exe
```

to obtain as output the human readable list of values for each requested symbol:

```
{
  array = { 1, 4, 3 };
}
```

The above option is useful for the user and their preliminary analysis but does
not contain enough information for further computer-based analyses. To that end,
memory analyzer has an option to request the result to be a snapshot of the
whole symbol table `--symtab-snapshot`. Finally, to obtain an output in JSON
format, e.g. for further analyses by `goto-harness` pass the additional option
`--json-ui`.

```sh
$ memory-analyzer --symtab-snapshot --json-ui \
--breakpoint checkpoint --symbols array main_exe > snapshot.json
```
