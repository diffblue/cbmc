/*******************************************************************\

Module: Lint Examples

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

static void fun()
{
  // This should not produce a warning
  do
  {
    int x=0;
  }
  while(a);

  // This should
  while(b);

  // As should this
  if(true)
  {
    do_something();
  }
  while(c);
}
