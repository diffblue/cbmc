/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#include "ansi_c_declaration.h"

#include <ostream>

#include <util/config.h>
#include <util/invariant.h>
#include <util/std_types.h>
#include <util/symbol.h>

#include "merged_type.h"

void ansi_c_declaratort::build(irept &src)
{
  typet *p=static_cast<typet *>(&src);

  // walk down subtype until we hit typedef_type, symbol or "abstract"
  while(true)
  {
    typet &t=*p;

    if(t.id() == ID_typedef_type || t.id() == ID_symbol)
    {
      set_base_name(t.get(ID_C_base_name));
      add_source_location()=t.source_location();
      t.make_nil();
      break;
    }
    else if(t.id().empty() ||
            t.is_nil())
    {
      UNREACHABLE;
    }
    else if(t.id()==ID_abstract)
    {
      t.make_nil();
      break;
    }
    else if(t.id()==ID_merged_type)
    {
      // we always walk down the _last_ member of a merged type
      auto &merged_type = to_merged_type(t);
      p = &merged_type.last_type();
    }
    else
      p=&t.subtype();
  }

  type()=static_cast<const typet &>(src);
  value().make_nil();
}

void ansi_c_declarationt::output(std::ostream &out) const
{
  out << "Flags:";
  if(get_is_typedef())
    out << " is_typedef";
  if(get_is_enum_constant())
    out << " is_enum_constant";
  if(get_is_static())
    out << " is_static";
  if(get_is_parameter())
    out << " is_parameter";
  if(get_is_global())
    out << " is_global";
  if(get_is_register())
    out << " is_register";
  if(get_is_thread_local())
    out << " is_thread_local";
  if(get_is_inline())
    out << " is_inline";
  if(get_is_extern())
    out << " is_extern";
  if(get_is_static_assert())
    out << " is_static_assert";
  out << "\n";

  out << "Type: " << type().pretty() << "\n";

  for(const auto &declarator : declarators())
    out << "Declarator: " << declarator.pretty() << "\n";
}

typet ansi_c_declarationt::full_type(
  const ansi_c_declaratort &declarator) const
{
  typet result=declarator.type();
  typet *p=&result;

  // this gets types that are still raw parse trees
  while(p->is_not_nil())
  {
    if(p->id()==ID_frontend_pointer || p->id()==ID_array ||
       p->id()==ID_vector || p->id()==ID_c_bit_field ||
       p->id()==ID_block_pointer || p->id()==ID_code)
      p=&p->subtype();
    else if(p->id()==ID_merged_type)
    {
      // we always go down on the right-most subtype
      auto &merged_type = to_merged_type(*p);
      p = &merged_type.last_type();
    }
    else
      UNREACHABLE;
  }

  *p=type();

  // retain typedef for dump-c
  if(get_is_typedef())
    result.set(ID_C_typedef, declarator.get_name());

  return result;
}

void ansi_c_declarationt::to_symbol(
  const ansi_c_declaratort &declarator,
  symbolt &symbol) const
{
  symbol.clear();
  symbol.value=declarator.value();
  symbol.type=full_type(declarator);
  symbol.name=declarator.get_name();
  symbol.pretty_name=symbol.name;
  symbol.base_name=declarator.get_base_name();
  symbol.is_type=get_is_typedef();
  symbol.location=declarator.source_location();
  symbol.is_extern=get_is_extern();
  symbol.is_macro=get_is_typedef() || get_is_enum_constant();
  symbol.is_parameter=get_is_parameter();
  symbol.is_weak=get_is_weak();

  // is it a function?
  typet &type = symbol.type.id() == ID_merged_type
                  ? to_merged_type(symbol.type).last_type()
                  : symbol.type;

  if(type.id() == ID_code && !symbol.is_type)
  {
    symbol.is_static_lifetime=false;
    symbol.is_thread_local=false;

    symbol.is_file_local=get_is_static();

    if(get_is_inline())
      to_code_type(type).set_inlined(true);

    if(
      config.ansi_c.mode == configt::ansi_ct::flavourt::GCC ||
      config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG ||
      config.ansi_c.mode == configt::ansi_ct::flavourt::ARM)
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

      // GCC __attribute__((__used__)) - do not treat those as file-local
      if(get_is_used())
        symbol.is_file_local = false;
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
      (get_is_global() && get_is_static() && !get_is_used()) ||
      symbol.is_parameter;
  }
}
