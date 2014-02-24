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
      const loc_reft entry_loc=end();
      function_entry.first_loc=entry_loc;

      forall_goto_program_instructions(i_it, goto_function.body)
      {
        target_map[i_it]=end();
        loc_vector.push_back(loct(i_it, f_it->first));
      }
    }
    else
      function_entry.first_loc=loc_reft::nil();
  }
  
  if(function_map.find(ID_main)==function_map.end())
    throw "no entry point";
  
  entry_loc=function_map[ID_main].first_loc;
    
  // build branch targets
  for(unsigned l=0; l<loc_vector.size(); l++)
  {
    const goto_programt::instructiont &i=*loc_vector[l].target;

    if(i.targets.empty())
    {
    }
    else if(i.targets.size()==1)
    {
      const target_mapt::const_iterator m_it=target_map.find(i.get_target());

      if(m_it==target_map.end())
        throw "locst::build: jump target not found";

      const loc_reft target=m_it->second;

      if(target.loc_number>=loc_vector.size())
        throw "locst::build: illegal jump target";

      loc_vector[l].branch_target=target;
    }
    else
      throw "locst does not support more than one branch target";
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
              
    if(!loc.branch_target.is_nil())
      out << "    T: " << loc.branch_target << "\n";
  }
  
  out << "\n";
  out << "The entry location is L" << entry_loc << ".\n";
}

