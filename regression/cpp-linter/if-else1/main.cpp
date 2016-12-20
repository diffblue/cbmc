/*******************************************************************\

Module: Lint Examples

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

static void fun()
{
  bool condition=false;
  if(condition) {
    fun();
  } else if(condition) {
    fun();
  } else  {
    fun();
  }
}
