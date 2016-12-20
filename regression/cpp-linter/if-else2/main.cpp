/*******************************************************************\

Module: Lint Examples

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

static void fun()
{
  if(condition) {
    fun();
  }
  else if(condition) {
    fun();
  }
  else  {
    fun();
  }
}
