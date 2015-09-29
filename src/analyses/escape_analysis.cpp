/*******************************************************************\

Module: Field-insensitive, location-sensitive escape analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>

#include "escape_analysis.h"

#include <iostream>

/*******************************************************************\

Function: escape_domaint::get_function

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

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

/*******************************************************************\

Function: escape_domaint::assign_lhs_cleanup

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::assign_lhs_cleanup(
  const exprt &lhs,
  const std::set<irep_idt> &cleanup_functions)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    cleanup_map[identifier].cleanup_functions=cleanup_functions;
  }
}

/*******************************************************************\

Function: escape_domaint::assign_lhs_aliases

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::assign_lhs_aliases(
  const exprt &lhs,
  const std::set<irep_idt> &alias_set)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    aliases.isolate(identifier);
    for(std::set<irep_idt>::const_iterator it=alias_set.begin();
        it!=alias_set.end();
        it++)
    {
      aliases.make_union(identifier, *it);
    }
  }
}

/*******************************************************************\

Function: escape_domaint::get_rhs_cleanup

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::get_rhs_cleanup(
  const exprt &rhs,
  std::set<irep_idt> &cleanup_functions)
{
  if(rhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();

    const escape_domaint::cleanup_mapt::const_iterator m_it=
      cleanup_map.find(identifier);
    
    if(m_it!=cleanup_map.end())
      cleanup_functions.insert(m_it->second.cleanup_functions.begin(),
                               m_it->second.cleanup_functions.end());
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

/*******************************************************************\

Function: escape_domaint::get_rhs_aliases

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::get_rhs_aliases(
  const exprt &rhs,
  std::set<irep_idt> &alias_set)
{
  if(rhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();
    alias_set.insert(identifier);
    
    for(aliasest::const_iterator it=aliases.begin();
        it!=aliases.end();
        it++)
      if(aliases.same_set(*it, identifier))
        alias_set.insert(identifier);
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
}

/*******************************************************************\

Function: escape_domaint::transform

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  // upcast of ai
  //escape_analysist &ea=
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

      std::set<irep_idt> aliases;
      get_rhs_aliases(code_assign.rhs(), aliases);
      assign_lhs_aliases(code_assign.lhs(), aliases);
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
      const code_function_callt &code_function_call=to_code_function_call(instruction.code);
      const exprt &function=code_function_call.function();
      
      if(function.id()==ID_symbol)
      {
        const irep_idt &identifier=to_symbol_expr(function).get_identifier();
        if(identifier=="__CPROVER_cleanup")
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

              for(std::set<irep_idt>::const_iterator
                  l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
              {
                cleanup_map[*l_it].cleanup_functions.insert(cleanup_function);
              }
            }
          }
        }
      }
    }
    break;

  default:;
  }
}

/*******************************************************************\

Function: escape_domaint::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  for(cleanup_mapt::const_iterator it=cleanup_map.begin();
      it!=cleanup_map.end();
      it++)
  {
    out << it->first << ':';
    for(std::set<irep_idt>::const_iterator
        c_it=it->second.cleanup_functions.begin();
        c_it!=it->second.cleanup_functions.end();
        c_it++)
      out << ' ' << *c_it;
    out << '\n';
    
    out << "  Aliases:";
    for(cleanup_mapt::const_iterator it2=cleanup_map.begin();
        it2!=cleanup_map.end();
        it2++)
    {
      if(it->first==it2->first) continue;
      if(aliases.same_set(it->first, it2->first))
        out << ' ' << it2->first;
    }
    out << '\n';
  }
}

/*******************************************************************\

Function: escape_domaint::merge

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool escape_domaint::merge(
  const escape_domaint &b,
  locationt from,
  locationt to)
{
  bool changed=false;

  for(cleanup_mapt::const_iterator b_it=b.cleanup_map.begin();
      b_it!=b.cleanup_map.end();
      b_it++)
  {
    const std::set<irep_idt> &b_cleanup=b_it->second.cleanup_functions;
    std::set<irep_idt> &a_cleanup=cleanup_map[b_it->first].cleanup_functions;
    unsigned old_size=a_cleanup.size();
    a_cleanup.insert(b_cleanup.begin(), b_cleanup.end());
    if(a_cleanup.size()!=old_size) changed=true;
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
  for(aliasest::const_iterator it=aliases.begin();
      it!=aliases.end(); it++)
  {
    if(cleanup_map.find(*it)==cleanup_map.end())
      aliases.isolate(it);
  }
  
  return changed;
}

/*******************************************************************\

Function: escape_domaint::check_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::check_lhs(
  const exprt &lhs,
  std::set<irep_idt> &cleanup_functions)  
{
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(lhs).get_identifier();
    
    // does it have a cleanup function?
    const escape_domaint::cleanup_mapt::const_iterator m_it=
      cleanup_map.find(identifier);

    if(m_it!=cleanup_map.end())
    {
      // count the aliases

      unsigned count=0;
      
      for(aliasest::const_iterator
          a_it=aliases.begin();
          a_it!=aliases.end();
          a_it++)
      {
        if(*a_it!=identifier && aliases.same_set(*a_it, identifier))
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

/*******************************************************************\

Function: escape_analysist::instrument

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_analysist::insert_cleanup(
  goto_functionst::goto_functiont &goto_function,
  goto_programt::targett location,
  const exprt &lhs,
  const std::set<irep_idt> &cleanup_functions,
  const namespacet &ns)
{
  source_locationt source_location=location->source_location;
  
  for(std::set<irep_idt>::const_iterator c_it=cleanup_functions.begin();
      c_it!=cleanup_functions.end();
      c_it++)
  {
    symbol_exprt function=ns.lookup(*c_it).symbol_expr();
    const code_typet &function_type=to_code_type(function.type());
  
    goto_function.body.insert_before_swap(location);
    code_function_callt code;
    code.lhs().make_nil();
    code.function()=function;

    if(function_type.parameters().size()==1)
    {
      typet param_type=function_type.parameters().front().type();
      exprt arg=lhs;
      if(arg.type()!=param_type) arg.make_typecast(param_type);
      code.arguments().push_back(arg);
    }
    
    location->make_function_call(code);
    location->source_location=source_location;
  }
}

/*******************************************************************\

Function: escape_analysist::instrument

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_analysist::instrument(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      const goto_programt::instructiont &instruction=*i_it;

      switch(instruction.type)
      {
      case ASSIGN:
        {
          const code_assignt &code_assign=to_code_assign(instruction.code);
          
          std::set<irep_idt> cleanup_functions;
          operator[](i_it).check_lhs(code_assign.lhs(), cleanup_functions);
          insert_cleanup(f_it->second, i_it, code_assign.lhs(), cleanup_functions, ns);
        }
        break;

      case DEAD:
        {
          const code_deadt &code_dead=to_code_dead(instruction.code);

          std::set<irep_idt> cleanup_functions;
          operator[](i_it).check_lhs(code_dead.symbol(), cleanup_functions);          
          insert_cleanup(f_it->second, i_it, code_dead.symbol(), cleanup_functions, ns);
          
          for(unsigned i=0; i<cleanup_functions.size(); i++)
            i_it++;
        }
        break;

      default:;
      }
    }
  }
}
