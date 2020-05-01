[CPROVER Manual TOC](../../)

## Memory Analyzer

The memory analyzer is a front-end that runs and queries GDB in order to obtain
a snapshot of the state of the input program at a particular program location.
Such a snapshot could be useful on its own: to check the values of variables at
a particular program location. Furthermore, since the snapshot is a state of a
valid concrete execution, it can also be used for subsequent analyses.

## Usage

In order to analyze a program with `memory-analyzer` it needs to be compiled
with `goto-gcc` (assuming `goto-gcc` is on the `PATH`):

```sh
$ goto-gcc -g input_program.c -o input_program_exe
```

Calling `goto-gcc` instead of simply compiling with `gcc` or `goto-cc` produces
an ELF binary with a goto section that contains the goto model (goto program +
symbol table) [goto-cc-variants](../goto-cc/variants/).

The memory analyzer supports two ways of running GDB on the user code: either to
run the code from a core-file or up to a break-point. If the user already has a
core-file, they can specify it with the option `--core-file cf`. If the user
knows the point of their program from where they want to run the analysis, they
can specify it with the option `--breakpoint bp`. Only one of
core-file/break-point option can be used.

The tool also expects a comma-separated list of symbols to be analysed
`--symbols s1, s2, ...`. Given its dependence on GDB, `memory-analyzer` is a
Unix-only tool. The tool calls `gdb` to obtain the snapshot which is why the
`-g` option is necessary when compiling for the program symbols to be visible.

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
not contain enough information for further automated analyses. To that end,
memory analyzer has an option for the snapshot to be represented in the format
of a symbol table (with `--symtab-snapshot`). Finally, to obtain an output in
JSON format, e.g., for further analyses by `goto-harness` the additional option
`--json-ui` needs to be passed to `memory-analyzer`.

```sh
$ memory-analyzer --symtab-snapshot --json-ui \
--breakpoint checkpoint --symbols array main_exe > snapshot.json
```
