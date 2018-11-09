/*******************************************************************\

Module: Field-insensitive, location-sensitive escape analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-insensitive, location-sensitive escape analysis

#include "escape_analysis.h"

#include <util/cprover_prefix.h>
#include <util/simplify_expr.h>

bool escape_domaint::is_tracked(const symbol_exprt &symbol)
{
  const irep_idt &identifier=symbol.get_identifier();
  if(
    identifier == CPROVER_PREFIX "memory_leak" ||
    identifier == CPROVER_PREFIX "malloc_object" ||
    identifier == CPROVER_PREFIX "dead_object" ||
    identifier == CPROVER_PREFIX "deallocated")
  {
    return false;
  }

  return true;
}

irep_idt escape_domaint::get_function(const exprt &lhs)
{
  if(lhs.id()==ID_address_of)
    return get_function(to_address_of_expr(lhs).object());
  else if(lhs.id()==ID_typecast)
    return get_function(to_typecast_expr(lhs).op());
  else if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    return identifier;
  }

  return irep_idt();
}

void escape_domaint::assign_lhs_cleanup(
  const exprt &lhs,
  const std::set<irep_idt> &cleanup_functions)
{
  if(lhs.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(lhs);
    if(is_tracked(symbol_expr))
    {
      irep_idt identifier=symbol_expr.get_identifier();

      if(cleanup_functions.empty())
        cleanup_map.erase(identifier);
      else
        cleanup_map[identifier].cleanup_functions=cleanup_functions;
    }
  }
}

void escape_domaint::assign_lhs_aliases(
  const exprt &lhs,
  const std::set<irep_idt> &alias_set)
{
  if(lhs.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(lhs);
    if(is_tracked(symbol_expr))
    {
      irep_idt identifier=symbol_expr.get_identifier();

      aliases.isolate(identifier);

      for(const auto &alias : alias_set)
      {
        aliases.make_union(identifier, alias);
      }
    }
  }
}

void escape_domaint::get_rhs_cleanup(
  const exprt &rhs,
  std::set<irep_idt> &cleanup_functions)
{
  if(rhs.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(rhs);
    if(is_tracked(symbol_expr))
    {
      irep_idt identifier=symbol_expr.get_identifier();

      const escape_domaint::cleanup_mapt::const_iterator m_it=
        cleanup_map.find(identifier);

      if(m_it!=cleanup_map.end())
        cleanup_functions.insert(m_it->second.cleanup_functions.begin(),
                                 m_it->second.cleanup_functions.end());
    }
  }
  else if(rhs.id()==ID_if)
  {
    get_rhs_cleanup(to_if_expr(rhs).true_case(), cleanup_functions);
    get_rhs_cleanup(to_if_expr(rhs).false_case(), cleanup_functions);
  }
  else if(rhs.id()==ID_typecast)
  {
    get_rhs_cleanup(to_typecast_expr(rhs).op(), cleanup_functions);
  }
}

void escape_domaint::get_rhs_aliases(
  const exprt &rhs,
  std::set<irep_idt> &alias_set)
{
  if(rhs.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(rhs);
    if(is_tracked(symbol_expr))
    {
      irep_idt identifier=symbol_expr.get_identifier();
      alias_set.insert(identifier);

      for(const auto &alias : aliases)
        if(aliases.same_set(alias, identifier))
          alias_set.insert(alias);
    }
  }
  else if(rhs.id()==ID_if)
  {
    get_rhs_aliases(to_if_expr(rhs).true_case(), alias_set);
    get_rhs_aliases(to_if_expr(rhs).false_case(), alias_set);
  }
  else if(rhs.id()==ID_typecast)
  {
    get_rhs_aliases(to_typecast_expr(rhs).op(), alias_set);
  }
  else if(rhs.id()==ID_address_of)
  {
    get_rhs_aliases_address_of(to_address_of_expr(rhs).op0(), alias_set);
  }
}

void escape_domaint::get_rhs_aliases_address_of(
  const exprt &rhs,
  std::set<irep_idt> &alias_set)
{
  if(rhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();
    alias_set.insert("&"+id2string(identifier));
  }
  else if(rhs.id()==ID_if)
  {
    get_rhs_aliases_address_of(to_if_expr(rhs).true_case(), alias_set);
    get_rhs_aliases_address_of(to_if_expr(rhs).false_case(), alias_set);
  }
  else if(rhs.id()==ID_dereference)
  {
  }
}

void escape_domaint::transform(
  const irep_idt &,
  locationt from,
  const irep_idt &,
  locationt,
  ai_baset &,
  const namespacet &)
{
  if(has_values.is_false())
    return;

  // upcast of ai
  // escape_analysist &ea=
  //  static_cast<escape_analysist &>(ai);

  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);

      std::set<irep_idt> cleanup_functions;
      get_rhs_cleanup(code_assign.rhs(), cleanup_functions);
      assign_lhs_cleanup(code_assign.lhs(), cleanup_functions);

      std::set<irep_idt> rhs_aliases;
      get_rhs_aliases(code_assign.rhs(), rhs_aliases);
      assign_lhs_aliases(code_assign.lhs(), rhs_aliases);
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      aliases.isolate(code_decl.get_identifier());
      assign_lhs_cleanup(code_decl.symbol(), std::set<irep_idt>());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      aliases.isolate(code_dead.get_identifier());
      assign_lhs_cleanup(code_dead.symbol(), std::set<irep_idt>());
    }
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code_function_call=
        to_code_function_call(instruction.code);
      const exprt &function=code_function_call.function();

      if(function.id()==ID_symbol)
      {
        const irep_idt &identifier=to_symbol_expr(function).get_identifier();
        if(identifier == CPROVER_PREFIX "cleanup")
        {
          if(code_function_call.arguments().size()==2)
          {
            exprt lhs=code_function_call.arguments()[0];

            irep_idt cleanup_function=
              get_function(code_function_call.arguments()[1]);

            if(!cleanup_function.empty())
            {
              // may alias other stuff
              std::set<irep_idt> lhs_set;
              get_rhs_aliases(lhs, lhs_set);

              for(const auto &l : lhs_set)
              {
                cleanup_map[l].cleanup_functions.insert(cleanup_function);
              }
            }
          }
        }
      }
    }
    break;

  case END_FUNCTION:
    // This is the edge to the call site.
    break;

  default:
    {
    }
  }
}

void escape_domaint::output(
  std::ostream &out,
  const ai_baset &,
  const namespacet &) const
{
  if(has_values.is_known())
  {
    out << has_values.to_string() << '\n';
    return;
  }

  for(const auto &cleanup : cleanup_map)
  {
    out << cleanup.first << ':';
    for(const auto &id : cleanup.second.cleanup_functions)
      out << ' ' << id;
    out << '\n';
  }

  for(aliasest::const_iterator a_it1=aliases.begin();
      a_it1!=aliases.end();
      a_it1++)
  {
    bool first=true;

    for(aliasest::const_iterator a_it2=aliases.begin();
        a_it2!=aliases.end();
        a_it2++)
    {
      if(aliases.is_root(a_it1) && a_it1!=a_it2 &&
         aliases.same_set(a_it1, a_it2))
      {
        if(first)
        {
          out << "Aliases: " << *a_it1;
          first=false;
        }
        out << ' ' << *a_it2;
      }
    }

    if(!first)
      out << '\n';
  }
}

bool escape_domaint::merge(
  const escape_domaint &b,
  locationt,
  locationt)
{
  bool changed=has_values.is_false();
  has_values=tvt::unknown();

  for(const auto &cleanup : b.cleanup_map)
  {
    const std::set<irep_idt> &b_cleanup=cleanup.second.cleanup_functions;
    std::set<irep_idt> &a_cleanup=cleanup_map[cleanup.first].cleanup_functions;
    auto old_size=a_cleanup.size();
    a_cleanup.insert(b_cleanup.begin(), b_cleanup.end());
    if(a_cleanup.size()!=old_size)
      changed=true;
  }

  // kill empty ones

  for(cleanup_mapt::iterator a_it=cleanup_map.begin();
      a_it!=cleanup_map.end();
      ) // no a_it++
  {
    if(a_it->second.cleanup_functions.empty())
      a_it=cleanup_map.erase(a_it);
    else
      a_it++;
  }

  // do union
  for(aliasest::const_iterator it=b.aliases.begin();
      it!=b.aliases.end(); it++)
  {
    irep_idt b_root=b.aliases.find(it);

    if(!aliases.same_set(*it, b_root))
    {
      aliases.make_union(*it, b_root);
      changed=true;
    }
  }

  // isolate non-tracked ones
  #if 0
  for(aliasest::const_iterator it=aliases.begin();
      it!=aliases.end(); it++)
  {
    if(cleanup_map.find(*it)==cleanup_map.end())
      aliases.isolate(it);
  }
  #endif

  return changed;
}

void escape_domaint::check_lhs(
  const exprt &lhs,
  std::set<irep_idt> &cleanup_functions)
{
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(lhs).get_identifier();

    // pointer with cleanup function?
    const escape_domaint::cleanup_mapt::const_iterator m_it=
      cleanup_map.find(identifier);

    if(m_it!=cleanup_map.end())
    {
      // count the aliases

      std::size_t count=0;

      for(const auto &alias : aliases)
      {
        if(alias!=identifier && aliases.same_set(alias, identifier))
          count+=1;
      }

      // There is an alias? Then we are still ok.
      if(count==0)
      {
        cleanup_functions.insert(
          m_it->second.cleanup_functions.begin(),
          m_it->second.cleanup_functions.end());
      }
    }
  }
}

void escape_analysist::insert_cleanup(
  goto_functionst::goto_functiont &goto_function,
  goto_programt::targett location,
  const exprt &lhs,
  const std::set<irep_idt> &cleanup_functions,
  bool is_object,
  const namespacet &ns)
{
  source_locationt source_location=location->source_location;

  for(const auto &cleanup : cleanup_functions)
  {
    symbol_exprt function=ns.lookup(cleanup).symbol_expr();
    const code_typet &function_type=to_code_type(function.type());

    goto_function.body.insert_before_swap(location);
    code_function_callt code(function);
    code.function().add_source_location()=source_location;

    if(function_type.parameters().size()==1)
    {
      typet param_type=function_type.parameters().front().type();
      exprt arg=lhs;
      if(is_object)
        arg=address_of_exprt(arg);
      if(arg.type()!=param_type)
        arg.make_typecast(param_type);
      code.arguments().push_back(arg);
    }

    location->make_function_call(code);
    location->source_location=source_location;
  }
}

void escape_analysist::instrument(
  goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      get_state(i_it);

      const goto_programt::instructiont &instruction=*i_it;

      switch(instruction.type)
      {
      case ASSIGN:
        {
          const code_assignt &code_assign=to_code_assign(instruction.code);

          std::set<irep_idt> cleanup_functions;
          operator[](i_it).check_lhs(code_assign.lhs(), cleanup_functions);
          insert_cleanup(
            f_it->second,
            i_it,
            code_assign.lhs(),
            cleanup_functions,
            false,
            ns);
        }
        break;

      case DEAD:
        {
          const code_deadt &code_dead=to_code_dead(instruction.code);

          std::set<irep_idt> cleanup_functions1;

          escape_domaint &d=operator[](i_it);

          const escape_domaint::cleanup_mapt::const_iterator m_it=
            d.cleanup_map.find("&"+id2string(code_dead.get_identifier()));

          // does it have a cleanup function for the object?
          if(m_it!=d.cleanup_map.end())
          {
            cleanup_functions1.insert(
              m_it->second.cleanup_functions.begin(),
              m_it->second.cleanup_functions.end());
          }

          std::set<irep_idt> cleanup_functions2;

          d.check_lhs(code_dead.symbol(), cleanup_functions2);

          insert_cleanup(
            f_it->second,
            i_it,
            code_dead.symbol(),
            cleanup_functions1,
            true,
            ns);
          insert_cleanup(
            f_it->second,
            i_it,
            code_dead.symbol(),
            cleanup_functions2,
            false,
            ns);

          for(const auto &c : cleanup_functions1)
          {
            (void)c;
            i_it++;
          }

          for(const auto &c : cleanup_functions2)
          {
            (void)c;
            i_it++;
          }
        }
        break;

      default:
        {
        }
      }
    }

    Forall_goto_program_instructions(i_it, f_it->second.body)
      get_state(i_it);
  }
}
