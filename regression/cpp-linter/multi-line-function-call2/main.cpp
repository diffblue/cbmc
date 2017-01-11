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
  // Incorrect, call should be on a new line
  nested(call(),
    another_param);

  // Incorrect - should be indented by 2
  nested(
         call(),
         another_param);

  // Correct
  nested(
    call(),
    another_param);

  // Correct
  twice(
    nested(
      call(
        param1),
      param2),
    param3)

  // Correct
  foo(
    bar(x, y),
    z);

  // Correct
  foo(
    bar(
      x,
      y),
    z);

  // Incorrect, the bar arguments have been split up therefore
  // they all should be split up
  foo(
    bar(x,
      y),
    z);

  // Incorrect bar should be on the next line
  foo(bar(x, y),
    z);
}
