/*******************************************************************\

Module: Program Locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "locs.h"

/*******************************************************************\

Function: locst::locst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

locst::locst(
  const namespacet &_ns):
  ns(_ns)
{
}

/*******************************************************************\

Function: locst::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void locst::build(const goto_functionst &goto_functions)
{
  // build locations

  typedef std::map<goto_programt::const_targett,
                   loc_reft> target_mapt;

  target_mapt target_map;
  
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functionst::goto_functiont &goto_function = f_it->second;

    function_entryt &function_entry=function_map[f_it->first];
    function_entry.type=goto_function.type;

    if(goto_function.body_available)
    {
      const loc_reft entry_loc=next_free_loc();
      function_entry.first_loc=entry_loc;

      forall_goto_program_instructions(i_it, goto_function.body)
      {
        target_map[i_it]=next_free_loc();
        loc_vector.push_back(loct(i_it, f_it->first));
      }
    }
    else
      function_entry.first_loc=loc_reft::nil();
  }
  
  if(function_map.find(ID_main)==function_map.end())
    throw "no entry point";
  
  entry_loc=function_map[ID_main].first_loc;
    
  // build targets
  for(unsigned l=0; l<loc_vector.size(); l++)
  {
    const goto_programt::instructiont &i=*loc_vector[l].target;

    loc_vector[l].targets.reserve(i.targets.size());
  
    for(goto_programt::instructiont::targetst::const_iterator
        t_it=i.targets.begin();
        t_it!=i.targets.end();
        t_it++)
    {
      const target_mapt::const_iterator m_it=target_map.find(*t_it);
      if(m_it==target_map.end())
        throw "locst::build: jump target not found";

      const loc_reft target=m_it->second;

      if(target.loc_number>=loc_vector.size())
        throw "locst::build: illegal jump target";

      loc_vector[l].targets.push_back(target);
    }
  }
}

/*******************************************************************\

Function: locst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void locst::output(std::ostream &out) const
{
  irep_idt function;

  for(unsigned l=0; l<loc_vector.size(); l++)
  {
    const loct &loc=loc_vector[l];
    if(function!=loc.function)
    {
      function=loc.function;
      out << "*** " << function << "\n";
    }
   
    out << "  L" << l << ": "
//        << loc.target->type << " "
//        << loc.target->location
        << " " << as_string(ns, *loc.target) << "\n";
              
    if(!loc.targets.empty())
    {
      out << "    T:";
      for(loct::targetst::const_iterator
          t_it=loc.targets.begin();
          t_it!=loc.targets.end();
          t_it++)
        out << " " << *t_it;
      out << "\n";
    }
  }
  
  out << "\n";
  out << "The entry location is L" << entry_loc << ".\n";
}

