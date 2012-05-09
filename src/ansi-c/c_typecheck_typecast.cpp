/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>

#include "c_typecast.h"
#include "c_typecheck_base.h"
#include "c_types.h"

/*******************************************************************\

Function: c_typecheck_baset::implicit_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::implicit_typecast(
  exprt &expr,
  const typet &dest_type)
{
  c_typecastt c_typecast(*this);
  
  typet src_type=expr.type();
  
  c_typecast.implicit_typecast(expr, dest_type);

  for(std::list<std::string>::const_iterator
      it=c_typecast.errors.begin();
      it!=c_typecast.errors.end();
      it++)
  {
    err_location(expr);
    str << "in expression `" << to_string(expr) << "':\n";
    str << "conversion from `"
        << to_string(src_type) << "' to `"
        << to_string(dest_type) << "': "
        << *it;
    error();
  }
  
  if(!c_typecast.errors.empty())
    throw 0; // give up
  
  for(std::list<std::string>::const_iterator
      it=c_typecast.warnings.begin();
      it!=c_typecast.warnings.end();
      it++)
  {
    err_location(expr);
    str << "warning: conversion from `"
        << to_string(src_type)
        << "' to `"
        << to_string(dest_type)
        << "': " << *it;
    warning();
  }
}

/*******************************************************************\

Function: c_typecheck_baset::implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::implicit_typecast_arithmetic(
  exprt &expr1,
  exprt &expr2)
{
  c_typecastt c_typecast(*this);
  c_typecast.implicit_typecast_arithmetic(expr1, expr2);
}

/*******************************************************************\

Function: c_typecheck_baset::implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::implicit_typecast_arithmetic(exprt &expr)
{
  c_typecastt c_typecast(*this);
  c_typecast.implicit_typecast_arithmetic(expr);
}
