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

Function: escape_domaint::set_cleanup

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::set_cleanup(
  const exprt &lhs,
  const irep_idt &function)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    cleanup_map[identifier].insert(function);
  }
}

/*******************************************************************\

Function: escape_domaint::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::assign_lhs(
  const exprt &lhs,
  const std::set<irep_idt> &cleanup_functions)
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    cleanup_map[identifier]=cleanup_functions;
  }
}

/*******************************************************************\

Function: escape_domaint::get_rhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_domaint::get_rhs(
  const exprt &rhs,
  std::set<irep_idt> &cleanup_functions)
{
  if(rhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();

    const escape_domaint::cleanup_mapt::const_iterator m_it=
      cleanup_map.find(identifier);
    
    if(m_it!=cleanup_map.end())
      cleanup_functions.insert(m_it->second.begin(), m_it->second.end());
  }
  else if(rhs.id()==ID_if)
  {
    get_rhs(to_if_expr(rhs).true_case(), cleanup_functions);
    get_rhs(to_if_expr(rhs).false_case(), cleanup_functions);
  }
  else if(rhs.id()==ID_typecast)
  {
    get_rhs(to_typecast_expr(rhs).op(), cleanup_functions);
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
  escape_analysist &ea=
    static_cast<escape_analysist &>(ai);

  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);
      
      std::set<irep_idt> cleanup_functions;
      get_rhs(code_assign.rhs(), cleanup_functions);

      // may alias other stuff
      std::set<exprt> lhs_set=
        ea.local_may_alias_factory(from).get(from, code_assign.lhs());

      for(std::set<exprt>::const_iterator
          l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
      {
        assign_lhs(*l_it, cleanup_functions);
      }
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      assign_lhs(code_decl.symbol(), std::set<irep_idt>());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      assign_lhs(code_dead.symbol(), std::set<irep_idt>());
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
              std::set<exprt> lhs_set=
                ea.local_may_alias_factory(from).get(from, lhs);

              for(std::set<exprt>::const_iterator
                  l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
              {
                set_cleanup(*l_it, cleanup_function);
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
    for(std::set<irep_idt>::const_iterator c_it=it->second.begin();
        c_it!=it->second.end();
        c_it++)
      out << ' ' << *c_it;
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
    const std::set<irep_idt> &b_cleanup=b_it->second;
    std::set<irep_idt> &a_cleanup=cleanup_map[b_it->first];
    unsigned old_size=a_cleanup.size();
    a_cleanup.insert(b_cleanup.begin(), b_cleanup.end());
    if(a_cleanup.size()!=old_size) changed=true;
  }

  return changed;
}

/*******************************************************************\

Function: escape_analysist::check_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void escape_analysist::check_lhs(
  locationt location,
  const exprt &lhs,
  std::set<irep_idt> &cleanup_functions)  
{
  if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();
    
    // does it have a cleanup function?
    const escape_domaint::cleanup_mapt &cleanup_map=
      operator[](location).cleanup_map;
      
    const escape_domaint::cleanup_mapt::const_iterator m_it=
      cleanup_map.find(identifier);
    
    if(m_it!=cleanup_map.end())
    {
      std::set<exprt> lhs_set=
        local_may_alias_factory(location).get(location, lhs);

      // more than one?
      if(lhs_set.size()<=1)
      {
        cleanup_functions.insert(m_it->second.begin(), m_it->second.end());
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
  for(std::set<irep_idt>::const_iterator c_it=cleanup_functions.begin();
      c_it!=cleanup_functions.end();
      c_it++)
  {
    goto_function.body.insert_before_swap(location);
    code_function_callt code;
    code.lhs().make_nil();
    code.function()=ns.lookup(*c_it).symbol_expr();
    location->make_function_call(code);
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
          
          // may alias other stuff
          std::set<exprt> lhs_set=
            local_may_alias_factory(i_it).get(i_it, code_assign.lhs());

          for(std::set<exprt>::const_iterator
              l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
          {
            std::set<irep_idt> cleanup_functions;
            check_lhs(i_it, *l_it, cleanup_functions);

            insert_cleanup(f_it->second, i_it, *l_it, cleanup_functions, ns);
          }
        }
        break;

      case DEAD:
        {
          const code_deadt &code_dead=to_code_dead(instruction.code);
          std::set<irep_idt> cleanup_functions;
          check_lhs(i_it, code_dead.symbol(), cleanup_functions);

          insert_cleanup(f_it->second, i_it, code_dead.symbol(), cleanup_functions, ns);
        }
        break;

      default:;
      }
    }
  }
}
