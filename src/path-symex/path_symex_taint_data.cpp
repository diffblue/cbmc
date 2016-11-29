/*******************************************************************
 Module: Taint Data Module

 Author: Daniel Neville, daniel.neville@cs.ox.ac.uk
 John Galea,		john.galea@cs.ox.ac.uk

 \*******************************************************************/

#include "path_symex_taint_data.h"

taint_datat::taint_rulet::taint_rulet()
{
  loc=0;
  // 0 = TOP element, always.
  taint=0;
  symbol_flag=false;
  symbol_name="";
}

/*******************************************************************

 Function: taint_datat::taint_rulet::output

 Inputs: Takes Output stream and taint engine.

 Outputs: Returns nothing.

 Purpose: Outputs to stream the specified rule.

 \*******************************************************************/

void taint_datat::taint_rulet::output(taint_enginet &taint_engine,
    std::ostream &out) const
{
  out << "Location: " << loc;
  if(symbol_flag)
    out << ", symbol name: " << symbol_name;

  out << " set to " << taint_engine.get_taint_name(taint);
}

taint_datat::taint_datat()
{
}
;

/*******************************************************************

 Function: taint_datat::add

 Inputs: The location where a given taint state is introduced.

 Outputs: Nothing

 Purpose: Registers a taint rule, normally parsed from the JSON file.

 \*******************************************************************/

void taint_datat::add(unsigned loc, taintt taint, bool symbol_flag,
    irep_idt symbol_name)
{
  taint_rulet rule;
  rule.loc=loc;
  rule.taint=taint;
  rule.symbol_name=symbol_name;
  rule.symbol_flag=symbol_flag;
  data[loc].push_back(rule);
}

/*******************************************************************

 Function: taint_datat::check_rules

 Inputs: Takes the locs of the program.

 Outputs: Returns true in case a rule is invalid

 Purpose: Checks specified taint introduction rules.

 This is not intended to be a complete checker of rules.

 \*******************************************************************/

bool taint_datat::check_rules(locst &locs, std::ostream & warning,
    taint_enginet &taint_engine)
{
  if(!taint_engine.enabled)
    return false;

  for (auto rule_vector : data)
  {
    for (auto rule : rule_vector.second)
    {
      // Check whether the rule is outside program.
      if(rule.loc >= locs.size())
      {
        warning << "Following rule outside program scope:" << "\n";
        rule.output(taint_engine, warning);
        warning << "\n";
        return true;
      }

      // Retrieve instruction.
      goto_programt::const_targett inst=locs.loc_vector[rule.loc].target;

      // Check that the instruction is supported.
      if(!inst->is_assign() && !inst->is_decl() && !inst->is_function_call())
      {

        warning << "Following rule refers to an unsupported op (" << inst->type
            << ")\n";
        rule.output(taint_engine, warning);
        warning << "\n";
        return true;

      }
      else if(inst->is_function_call())
      {
        // Need to check that the left hand side of the function call exists.
        code_function_callt function_call=to_code_function_call(inst->code);

        if(function_call.lhs().is_nil())
        {
          warning
              << "Following rule refers to function call with nil left-hand side:"
              << "\n";
          rule.output(taint_engine, warning);
          warning << "\n";
          return true;
        }
      }
    }
  }

  // No errors found.
  return false;
}

/*******************************************************************

 Function: taint_datat::check_rules

 Inputs: Takes Output stream.

 Outputs: Returns nothing.

 Purpose: Outputs to stream the specified rules.

 \*******************************************************************/

void taint_datat::output(std::ostream &out, taint_enginet &taint_engine) const
{
  int i=0;
  for (auto rule_vector : data)
  {
    for (auto rule : rule_vector.second)
    {
      out << ++i << ": ";
      rule.output(taint_engine, out);
      out << "\n";
    }
  }
}

