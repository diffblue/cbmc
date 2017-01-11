/*******************************************************************\

Module: Lint Examples

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

/*******************************************************************\

Function: fun

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void fun()
{
  // Correct
  foo(
    x,
    y);

  // Incorrect, x should be on the next line
  foo(x,
    y);

  // Incorrect indent should be only 2
  foo(
      x,
      y);

  // Correct
  int x=bar(
    x,
    y);

  // Incorrect, x should be on the next line
  int x=bar(x,
    y);

  // Incorrect indent should be only 2
  int x=bar(
      x,
      y);

  // Correct
  *model=baz(
    x,
    y);

  // Incorrect, x should be on the next line
  *model=baz(x,
    y);

  // Incorrect indent should be only 2
  *model=baz(
      x,
      y);

  // Correct
  var->fun(
    x,
    y);

  // Incorrect, x should be on the next line
  var->fun(x,
    y);

  // Incorrect indent should be only 2
  var->fun(
      x,
      y);

  // Incorrect
  fun(
    x, y);

  // Incorrect
  fun(
    x, y,
    z);
}

