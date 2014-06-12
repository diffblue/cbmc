/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/config.h>

#include "ansi_c_declaration.h"

/*******************************************************************\

Function: ansi_c_declaratort::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_declaratort::build(irept &src)
{
  typet *p=static_cast<typet *>(&src);
  
  // walk down subtype until we hit symbol or "abstract"
  while(true)
  {
    typet &t=*p;

    if(t.id()==ID_symbol)
    {
      set_base_name(t.get(ID_identifier));
      location()=t.location();
      t.make_nil();
      break;
    }
    else if(t.id()==irep_idt() ||
            t.is_nil())
    {
      //std::cerr << "D: " << src.pretty() << std::endl;
      assert(0);
    }
    else if(t.id()==ID_abstract)
    {
      t.make_nil();
      break;
    }
    else if(t.id()==ID_merged_type)
    {
      // we always walk down the _last_ member of a merged type
      assert(!t.subtypes().empty());
      p=&(t.subtypes().back());
    }
    else
      p=&t.subtype();
  }
  
  type()=static_cast<const typet &>(src);
  value().make_nil();
}

/*******************************************************************\

Function: ansi_c_declarationt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_declarationt::output(std::ostream &out) const
{
  out << "Flags:";
  if(get_is_type()) out << " is_type";
  if(get_is_typedef()) out << " is_typedef";
  if(get_is_enum_constant()) out << " is_enum_constant";
  if(get_is_static()) out << " is_static";
  if(get_is_parameter()) out << " is_parameter";
  if(get_is_global()) out << " is_global";
  if(get_is_register()) out << " is_register";
  if(get_is_thread_local()) out << " is_thread_local";
  if(get_is_inline()) out << " is_inline";
  if(get_is_extern()) out << " is_extern";
  if(get_is_static_assert()) out << " is_static_assert";
  out << "\n";

  out << "Type: " << type().pretty() << "\n";
  
  for(declaratorst::const_iterator d_it=declarators().begin();
      d_it!=declarators().end();
      d_it++)
    out << "Declarator: " << d_it->pretty() << "\n";
}

/*******************************************************************\

Function: ansi_c_declarationt::full_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet ansi_c_declarationt::full_type(
  const ansi_c_declaratort &declarator) const
{
  typet result=declarator.type();
  typet *p=&result;
  
  while(p->is_not_nil())
  {
    if(p->id()==ID_merged_type)
    {
      // we always walk down the last type in a merged_type
      p=&p->subtypes().back();
    }
    else
    {
      assert(p->id()==ID_pointer || p->id()==ID_array || p->id()==ID_code);
      p=&p->subtype();
    }
  }
  
  *p=type();
  return result;
}

/*******************************************************************\

Function: ansi_c_declarationt::to_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_declarationt::to_symbol(
  const ansi_c_declaratort &declarator,
  symbolt &symbol) const
{
  symbol.clear();    
  symbol.value=declarator.value();
  symbol.type=full_type(declarator);
  symbol.name="c::"+id2string(declarator.get_name());
  symbol.base_name=declarator.get_base_name();
  symbol.is_type=get_is_type();
  if(symbol.is_type)
    symbol.location=symbol.type.location();
  else
    symbol.location=location();
  symbol.is_extern=get_is_extern();
  symbol.is_macro=get_is_typedef() || get_is_enum_constant();
  symbol.is_parameter=get_is_parameter();

  bool is_code=symbol.type.id()==ID_code;

  symbol.is_static_lifetime=
    !symbol.is_macro &&
    !symbol.is_type &&
    (get_is_global() || get_is_static()) &&
    !is_code;
    
  symbol.is_thread_local=
    (!get_is_global() && !is_code &&
     !get_is_static() && !symbol.is_type &&
     !symbol.is_macro) ||
    (get_is_global() && !is_code && get_is_thread_local());
     
  symbol.is_file_local=
    get_is_static() || symbol.is_macro || 
    (!get_is_global() && !get_is_extern() && !is_code);
  
  if(get_is_inline())
    symbol.type.set(ID_C_inlined, true);

  // GCC extern inline cleanup, to enable remove_internal_symbols
  // do its full job
  // https://gcc.gnu.org/ml/gcc/2006-11/msg00006.html
  if(is_code && get_is_inline())
  {
    // __attribute__((__gnu_inline__))
    if(get_is_static() && get_is_extern())
      symbol.is_extern=false;
    // C99 and above
    else if(config.ansi_c.for_has_scope ||
            (config.ansi_c.mode!=configt::ansi_ct::MODE_GCC_C &&
             config.ansi_c.mode!=configt::ansi_ct::MODE_ARM_C_CPP))
      symbol.is_file_local=symbol.is_file_local || !get_is_extern();
    // traditional GCC
    else
      symbol.is_file_local=symbol.is_file_local || get_is_extern();
  }
}
