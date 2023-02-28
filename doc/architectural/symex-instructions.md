# Symex and GOTO program instructions

In [doc/central-data-structures](central-data-structures.md) we talked about
the relationship between various central data structures of CBMC.

We identified the `goto_programt` as being the core data structure representing
GOTO-IR, which we defined as a list of GOTO program instructions.

As a reminder, instructions are composed of three subcomponents:

* An instruction type,
* A statement (denoting the actual code the instruction contains),
* An instruction guard (an expression that needs to be evaluated to `true` before
  the instruction is to be executed - if one is attached to the instruction).

In this document, we are going to take a closer look at the first subcomponent,
the instruction types, along with the interplay between the instructions and a
central CBMC module, the *symbolic execution engine* (from now on, just *symex*).

## A (very) short introduction to Symex

Symex is, at its core, a GOTO-program interpreter that uses symbolic values instead of actual ones.
This produces a formula which describes all possible outputs rather than a single output value.
While Symex is interpreting the program, it also builds a list of Static Single Assignment (SSA)
steps that form part of the equation that is to be sent to the solver. For more information see
[src/goto-symex](../../src/goto-symex/README.md).

You can see the main instruction dispatcher (what corresponds to the main interpreter
loop) at `goto_symext::execute_next_instruction`.

Symex's source code is available under [src/goto-symex](../../src/goto-symex/).

## Instruction Types

Every GOTO-program instruction has a specific type. You can see the instruction type
at #goto_program_instruction_typet but we will also list some of them here for illustration
purposes:

```c
enum goto_program_instruction_typet
{
  [...]
  GOTO = 1,              // branch, possibly guarded
  ASSUME = 2,            // assumption
  ASSERT = 3,            // assertions
  SKIP = 5,              // just advance the PC
  SET_RETURN_VALUE = 12, // set function return value (no control-flow change)
  ASSIGN = 13,           // assignment lhs:=rhs
  DECL = 14,             // declare a local variable
  DEAD = 15,             // marks the end-of-live of a local variable
  FUNCTION_CALL = 16,    // call a function
  [...]
};
```

(*NOTE*: The above is for illustration purposes only - the list is not complete, neither is it
expected to be kept up-to-date. Please refer to the type #goto_program_instruction_typet for a
list of what the instructions look like at this point in time.)

You can observe these instruction types in the user-friendly print of the goto-program that
various CPROVER programs produce with the flag `--show-goto-functions`. For a live example,
consider the following C file:

```c
int main(int argc, char **argv)
{
    int a[] = {0, 1, 2, 3};
    __CPROVER_assert(a[3] != 3, "expected failure: last element of array 'a' is equal to 3");
}
```

If we ask CBMC to print the GOTO-program instructions with `--show-goto-functions`, then part
of the output looks like this:

```c
[...]

main /* main */
  // 0 file /tmp/example.c line 3 function main
  DECL main::1::arry : signedbv[32][4]
  // 1 file /tmp/example.c line 3 function main
  ASSIGN main::1::arry := { 0, 1, 2, 3 }
  // 2 file /tmp/example.c line 4 function main
  ASSERT main::1::arry[cast(3, signedbv[64])] ≠ 3 // expected failure: last arry element is equal to 3
  // 3 file /tmp/example.c line 5 function main
  DEAD main::1::arry
  // 4 file /tmp/example.c line 5 function main
  SET RETURN VALUE side_effect statement="nondet" is_nondet_nullable="1"
  // 5 file /tmp/example.c line 5 function main
  END_FUNCTION
```

In the above excerpt, the capitalised words at the beginning each instruction are the
correspondent instruction types (`DECL`, `ASSIGN`, etc).

---

Symex (as mentioned above) is going to pick a designated entry point and then start going through
each instruction. This happens at `goto_symext::execute_next_instruction`. While doing so, it will
inspect the instruction's type, and then dispatch to a designated handling function (which usually
go by the name `symex_<instruction-type>`) to handle that particular instruction type and its
symbolic execution. In pseudocode, it looks like this:

```c
switch(instruction.type())
{
  [...]

case GOTO:
  symex_goto(state);
  break;

case ASSUME:
  symex_assume(state, instruction.condition());
  break;
```

The way the [`symex` subfolder](../../src/goto-symex/) is structured, the different
dispatching functions are usually in their own file, designated by the instruction's
name. As an example, you can find the code for the function goto_symext::symex_goto
in [symex_goto.cpp](../../src/goto-symex/symex_goto.cpp)

The output of symex is an symex_target_equationt which consists of equalities between
different expressions in the program. You can visualise it as a data structure that
serialises to this: `(a = 5 ∨ a = 3) ∧ (b = 3) ∧ (c = 4) ∧ ...` that describe assignments
and conditions for a range of possible executions of a program that cover a range of
potential paths within it.

This is a high-level overview of symex and goto-program instructions.
For more information (and a more robust introduction), please have a look
at \ref symbolic-execution.
