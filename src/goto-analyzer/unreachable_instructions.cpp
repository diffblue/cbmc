/*******************************************************************\

Module: List all unreachable instructions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

#include <sstream>

#include <util/json.h>

#include <analyses/cfg_dominators.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/compute_called_functions.h>

#include "unreachable_instructions.h"

typedef std::map<unsigned, goto_programt::const_targett> dead_mapt;

/*******************************************************************\

Function: unreachable_instructions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void unreachable_instructions(
  const goto_programt &goto_program,
  const namespacet &ns,
  dead_mapt &dest)
{
  cfg_dominatorst dominators;
  dominators(goto_program);

  for(cfg_dominatorst::cfgt::entry_mapt::const_iterator
      it=dominators.cfg.entry_map.begin();
      it!=dominators.cfg.entry_map.end();
      ++it)
  {
    if(it->first->is_dead() ||
       (it->first->is_assign() &&
        to_code_assign(it->first->code).lhs().get(ID_identifier)==
        "__CPROVER_dead_object"))
      continue;

    const cfg_dominatorst::cfgt::nodet &n=dominators.cfg[it->second];
    if(n.dominators.empty())
      dest.insert(std::make_pair(it->first->location_number,
                                 it->first));
  }
}

/*******************************************************************\

Function: all_unreachable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void all_unreachable(
  const goto_programt &goto_program,
  const namespacet &ns,
  dead_mapt &dest)
{
  forall_goto_program_instructions(it, goto_program)
    if(!it->is_end_function() &&
       !it->is_dead() &&
       !(it->is_assign() &&
         to_code_assign(it->code).lhs().get(ID_identifier)==
         "__CPROVER_dead_object"))
      dest.insert(std::make_pair(it->location_number, it));
}

/*******************************************************************\

Function: output_dead_plain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void output_dead_plain(
  const namespacet &ns,
  const goto_programt &goto_program,
  const dead_mapt &dead_map,
  std::ostream &os)
{
  assert(!goto_program.instructions.empty());
  goto_programt::const_targett end_function=
    goto_program.instructions.end();
  --end_function;
  assert(end_function->is_end_function());

  os << "\n*** " << end_function->function << " ***\n";

  for(dead_mapt::const_iterator it=dead_map.begin();
      it!=dead_map.end();
      ++it)
    goto_program.output_instruction(ns, "", os, it->second);
}

/*******************************************************************\

Function: add_to_json

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void add_to_json(
  const namespacet &ns,
  const goto_programt &goto_program,
  const dead_mapt &dead_map,
  jsont &dest)
{
  jsont &entry=dest.push_back(jsont(jsont::J_OBJECT));

  assert(!goto_program.instructions.empty());
  goto_programt::const_targett end_function=
    goto_program.instructions.end();
  --end_function;
  assert(end_function->is_end_function());

  entry.object.insert(
    std::make_pair(
      "function",
      jsont(id2string(end_function->function))));
  entry.object.insert(
    std::make_pair(
      "file name",
      jsont(id2string(end_function->source_location.get_file()))));

  jsont &dead_ins=
    entry.object.insert(
      std::make_pair(
        "unreachable instructions",
        jsont(jsont::J_ARRAY))).first->second;

  for(dead_mapt::const_iterator it=dead_map.begin();
      it!=dead_map.end();
      ++it)
  {
    std::ostringstream oss;
    goto_program.output_instruction(ns, "", oss, it->second);
    std::string s=oss.str();

    std::string::size_type n=s.find('\n');
    assert(n!=std::string::npos);
    s.erase(0, n+1);
    n=s.find_first_not_of(' ');
    assert(n!=std::string::npos);
    s.erase(0, n);
    assert(!s.empty());
    s.erase(s.size()-1);

    jsont &i_entry=dead_ins.push_back(jsont(jsont::J_OBJECT));
    i_entry.object.insert(
      std::make_pair(
        "source location",
        jsont(it->second->source_location.as_string())));
    i_entry.object.insert(std::make_pair("statement", jsont(s)));
  }
}

/*******************************************************************\

Function: unreachable_instructions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unreachable_instructions(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  const bool json,
  std::ostream &os)
{
  jsont json_result(jsont::J_ARRAY);

  std::set<irep_idt> called;
  compute_called_functions(goto_functions, called);

  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body_available()) continue;

    const goto_programt &goto_program=f_it->second.body;
    dead_mapt dead_map;

    if(called.find(f_it->first)!=called.end())
      unreachable_instructions(goto_program, ns, dead_map);
    else
      all_unreachable(goto_program, ns, dead_map);

    if(!dead_map.empty())
    {
      if(!json)
        output_dead_plain(ns, goto_program, dead_map, os);
      else
        add_to_json(ns, goto_program, dead_map, json_result);
    }
  }

  if(json && !json_result.array.empty())
    os << json_result << std::endl;
}

