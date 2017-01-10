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
  throw "a valid error";

  throw("too bracketed");
  throw ("too bracketed");

  throw "Too capitalised";
  throw("Too bracketed and capitalised");
}
