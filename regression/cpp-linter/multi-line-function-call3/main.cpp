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
  // Correct as for loop not function
  for(int x=0;
    x<10;
    ++x)
  {}

  // Correct as an if statement not a function
  if(a==b ||
    c==d)
  {
    do_something();
  }

  // Correct as ranged based for loop not function
  for(x:
    list)
  {}

  // Correct since if statement
  if(some_check(with, params)==
    some_value)
  {
    do_something();
  }

  // Correct since if statement
  if(condition_a&&
    (condition_b||
      condition_c))
  {
    do_something();
  }
}
