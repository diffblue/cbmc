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
  bool *x=nullptr; // Valid
  bool* x=nullptr; // Invalid

  int &x=nullptr; // Valid
  int& x=nullptr; // Invalid

  int y=at*bt; // Valid

  // Probably valid - could be a pointer to type yt or a
  // variable called yt multilied by z. Would have to know
  // it is a function call rather than a function declaration
  foo(
    x,
    yt*z);
}
