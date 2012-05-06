/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_types.h"

#include "find_symbols.h"

typedef enum { F_TYPE, F_EXPR, F_BOTH } kindt;

/*******************************************************************\

Function: find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest)
{
  find_symbols(src, dest, true, true);
}

/*******************************************************************\

Function: find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_symbols(
  const exprt &src,
  find_symbols_sett &dest,
  bool current,
  bool next)
{
  if((src.id()==ID_symbol && current) ||
     (src.id()==ID_next_symbol && next))
    dest.insert(src.get(ID_identifier));
  else
  {
    forall_operands(it, src)
      find_symbols(*it, dest, current, next);
  }
}

/*******************************************************************\

Function: has_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols,
  bool current,
  bool next)
{
  if((src.id()==ID_symbol && current) ||
     (src.id()==ID_next_symbol && next))
    return symbols.count(src.get(ID_identifier))!=0;
  else
  {
    forall_operands(it, src)
      if(has_symbol(*it, symbols, current, next))
        return true;
  }
  
  return false;
}

/*******************************************************************\

Function: has_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_symbol(
  const exprt &src,
  const find_symbols_sett &symbols)
{
  return has_symbol(src, symbols, true, true);
}

/*******************************************************************\

Function: find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_symbols(
  const exprt &src,
  std::set<exprt> &dest)
{
  if(src.id()==ID_symbol || src.id()==ID_next_symbol)
    dest.insert(src);
  else
  {
    forall_operands(it, src)
      find_symbols(*it, dest);
  }
}

/*******************************************************************\

Function: find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_symbols(kindt kind, const typet &src, find_symbols_sett &dest);

void find_symbols(kindt kind, const exprt &src, find_symbols_sett &dest)
{
  forall_operands(it, src)
    find_symbols(kind, *it, dest);
  
  find_symbols(kind, src.type(), dest);
  
  if(kind==F_BOTH || kind==F_EXPR)
    if(src.id()==ID_symbol ||
       src.id()==ID_next_symbol)
      dest.insert(src.get(ID_identifier));
}

/*******************************************************************\

Function: find_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_symbols(kindt kind, const typet &src, find_symbols_sett &dest)
{
  if(src.has_subtype())
    find_symbols(kind, src.subtype(), dest);

  forall_subtypes(it, src)
    find_symbols(kind, *it, dest);
    
  if(src.id()==ID_struct ||
     src.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=to_struct_union_type(src);
    const struct_union_typet::componentst &components=struct_union_type.components();

    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
      find_symbols(kind, *it, dest);
  } 
  else if(src.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(src);
    find_symbols(kind, code_type.return_type(), dest);
    const code_typet::argumentst &arguments=code_type.arguments();

    for(code_typet::argumentst::const_iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {
      find_symbols(kind, *it, dest);
      irep_idt identifier=it->get_identifier();
      if(identifier!=irep_idt() && (kind==F_TYPE || kind==F_BOTH))
        dest.insert(identifier);
    }
  }
  else if(src.id()==ID_symbol)
    dest.insert(src.get(ID_identifier));
  else if(src.id()==ID_array)
  {
    // do the size -- the subtype is already done
    find_symbols(kind, to_array_type(src).size(), dest);
  }
}

/*******************************************************************\

Function: find_type_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_type_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(F_TYPE, src, dest);
}

/*******************************************************************\

Function: find_type_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_type_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(F_TYPE, src, dest);
}

/*******************************************************************\

Function: find_type_and_expr_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_type_and_expr_symbols(const exprt &src, find_symbols_sett &dest)
{
  find_symbols(F_BOTH, src, dest);
}

/*******************************************************************\

Function: find_type_and_expr_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_type_and_expr_symbols(const typet &src, find_symbols_sett &dest)
{
  find_symbols(F_BOTH, src, dest);
}

