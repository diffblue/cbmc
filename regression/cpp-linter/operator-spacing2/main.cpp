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
  status() << "Adding CPROVER library (" << eom;

  int x = 1<<4;

  // Ideally this should produce an error, see operator-spacing3
  status()<<"Adding CPROVER library ("<<eom;

  // Ideally this should produce an error, see operator-spacing3
  int x = 1 << 4;

  int y = a<<b;
}
