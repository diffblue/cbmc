/*******************************************************************\

Module: Value Set Propagation (Flow Insensitive, Validity Regions)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

//#include <assert.h>

#include <prefix.h>
#include <cprover_prefix.h>
#include <xml_irep.h>
#include <context.h>

#include <langapi/language_util.h>

#include "value_set_analysis_fivrns.h"

/*******************************************************************\

Function: value_set_analysis_fivrnst::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysis_fivrnst::initialize(
  const goto_programt &goto_program)
{
  baset::initialize(goto_program);
  add_vars(goto_program);
}

/*******************************************************************\

Function: value_set_analysis_fivrnst::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysis_fivrnst::initialize(
  const goto_functionst &goto_functions)
{
  baset::initialize(goto_functions);
  add_vars(goto_functions);
}

/*******************************************************************\

Function: value_set_analysis_fivrnst::add_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysis_fivrnst::add_vars(
  const goto_programt &goto_program)
{
  typedef std::list<value_set_fivrnst::entryt> entry_listt;
  
  // get the globals
  entry_listt globals;
  get_globals(globals);
  
  // get the locals
  goto_programt::decl_identifierst locals;
  goto_program.get_decl_identifiers(locals);

  // cache the list for the locals to speed things up  
  typedef hash_map_cont<irep_idt, entry_listt, irep_id_hash> entry_cachet;
  entry_cachet entry_cache;
  
  value_set_fivrnst &v=state.value_set;

  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {    
    v.add_vars(globals);
    
    for(goto_programt::decl_identifierst::const_iterator
        l_it=locals.begin();
        l_it!=locals.end();
        l_it++)
    {
      // cache hit?
      entry_cachet::const_iterator e_it=entry_cache.find(*l_it);

      if(e_it==entry_cache.end())
      {
        const symbolt &symbol=ns.lookup(*l_it);
        
        std::list<value_set_fivrnst::entryt> &entries=entry_cache[*l_it];
        get_entries(symbol, entries);
        v.add_vars(entries);
      }
      else
        v.add_vars(e_it->second);
    }
  }
}

/*******************************************************************\

Function: value_set_analysis_fivrnst::get_entries

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysis_fivrnst::get_entries(
  const symbolt &symbol,
  std::list<value_set_fivrnst::entryt> &dest)
{
  get_entries_rec(symbol.name, "", symbol.type, dest);
}

/*******************************************************************\

Function: value_set_analysis_fivrnst::get_entries

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysis_fivrnst::get_entries_rec(
  const irep_idt &identifier,
  const std::string &suffix,
  const typet &type,
  std::list<value_set_fivrnst::entryt> &dest)
{
  const typet &t=ns.follow(type);

  if(t.id()=="struct" ||
     t.id()=="union")
  {
    const struct_typet &struct_type=to_struct_type(t);
    
    const struct_typet::componentst &c=struct_type.components();
    
    for(struct_typet::componentst::const_iterator
        it=c.begin();
        it!=c.end();
        it++)
    {
      get_entries_rec(
        identifier,
        suffix+"."+it->get_string("name"),
        it->type(),
        dest);
    }
  }
  else if(t.id()=="array")
  {
    get_entries_rec(identifier, suffix+"[]", t.subtype(), dest);
  }
  else if(check_type(t))
  {
    dest.push_back(value_set_fivrnst::entryt(identifier, suffix));
  }
}

/*******************************************************************\

Function: value_set_analysis_fivrnst::add_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysis_fivrnst::add_vars(
  const goto_functionst &goto_functions)
{
  // get the globals
  std::list<value_set_fivrnst::entryt> globals;
  get_globals(globals);
  
  value_set_fivrnst &v=state.value_set;

  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    // get the locals  
    std::set<irep_idt> locals;  
    get_local_identifiers(f_it->second, locals);  

    forall_goto_program_instructions(i_it, f_it->second.body)
    {    
      v.add_vars(globals);
      
      for(std::set<irep_idt>::const_iterator
          l_it=locals.begin();
          l_it!=locals.end();
          l_it++)
      {
        const symbolt &symbol=ns.lookup(*l_it);
        
        std::list<value_set_fivrnst::entryt> entries;
        get_entries(symbol, entries);
        v.add_vars(entries);
      }
    }
  }
}    

/*******************************************************************\

Function: value_set_analysis_fivrnst::get_globals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_analysis_fivrnst::get_globals(
  std::list<value_set_fivrnst::entryt> &dest)
{
  // static ones
  forall_symbols(it, ns.get_context().symbols)
    if(it->second.lvalue &&
       it->second.static_lifetime)
      get_entries(it->second, dest);
}    

/*******************************************************************\

Function: value_set_analysis_fivrnst::check_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_analysis_fivrnst::check_type(const typet &type)
{
    if(type.id()=="pointer")
    {
      switch(track_options) {
        case TRACK_ALL_POINTERS:
          { return true; break; }
        case TRACK_FUNCTION_POINTERS:
        {
          if(type.id()=="pointer")
          {
            const typet *t = &type;
            while (t->id()=="pointer") t = &(t->subtype());
                    
            return (t->id()=="code");
          }
          
          break;
        }
        default: // don't track. 
          break;
      }
    }
    else if(type.id()=="struct" ||
            type.id()=="union")
    {
      const struct_typet &struct_type=to_struct_type(type);
      
      const struct_typet::componentst &components=
        struct_type.components();
  
      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        if(check_type(it->type())) return true;
      }    
    }
    else if(type.id()=="array")
      return check_type(type.subtype());
    else if(type.id()=="symbol")
      return check_type(ns.follow(type));
  
  return false;      
}    
