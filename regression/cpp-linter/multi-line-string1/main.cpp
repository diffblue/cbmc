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
  auto fn_prettyname=id2string(arg0.get(ID_C_class))
    .substr(java_prefix.size())
    +"."+id2string(fn_basename)+"()";

  auto fn_prettyname=id2string(arg0.get(ID_C_class))
    .substr(java_prefix.size())+
    "."+id2string(fn_basename)+"()";
}
