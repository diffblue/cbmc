/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>
#include <cassert>

#include <util/config.h>
#include <util/std_types.h>

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
      set_base_name(t.get(ID_C_base_name));
      add_source_location()=t.source_location();
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

  // this gets types that are still raw parse trees
  while(p->is_not_nil())
  {
    if(p->id()==ID_pointer || p->id()==ID_array || 
       p->id()==ID_vector || p->id()==ID_c_bit_field ||
       p->id()==ID_block_pointer || p->id()==ID_code)
      p=&p->subtype();
    else if(p->id()==ID_merged_type)
    {
      // we always go down on the right-most subtype
      assert(!p->subtypes().empty());
      p=&(p->subtypes().back());
    }
    else
      assert(false);
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
  symbol.name=declarator.get_name();
  symbol.base_name=declarator.get_base_name();
  symbol.is_type=get_is_typedef();
  symbol.location=declarator.source_location();
  symbol.is_extern=get_is_extern();
  symbol.is_macro=get_is_typedef() || get_is_enum_constant();
  symbol.is_parameter=get_is_parameter();
  
  // is it a function?
  
  if(symbol.type.id()==ID_code && !symbol.is_type)
  {
    symbol.is_static_lifetime=false;
    symbol.is_thread_local=false;

    symbol.is_file_local=get_is_static();
    
    if(get_is_inline())
      symbol.type.set(ID_C_inlined, true);

    if(config.ansi_c.mode==configt::ansi_ct::MODE_GCC_C ||
       config.ansi_c.mode==configt::ansi_ct::MODE_ARM_C_CPP)
    {
      // GCC extern inline cleanup, to enable remove_internal_symbols
      // do its full job
      // https://gcc.gnu.org/ml/gcc/2006-11/msg00006.html
      // __attribute__((__gnu_inline__))
      if(get_is_inline())
      {
        if(get_is_static()) // C99 and above
          symbol.is_extern=false;
        else  if(get_is_extern()) // traditional GCC
          symbol.is_file_local=true;
      }
    }
  }
  else // non-function
  {
    symbol.is_static_lifetime=
      !symbol.is_macro &&
      !symbol.is_type &&
      (get_is_global() || get_is_static());
      
    symbol.is_thread_local=
      (!symbol.is_static_lifetime && !get_is_extern()) ||
      get_is_thread_local();
       
    symbol.is_file_local=
      symbol.is_macro || 
      (!get_is_global() && !get_is_extern()) ||
      (get_is_global() && get_is_static()) ||
      symbol.is_parameter;
  }
}
