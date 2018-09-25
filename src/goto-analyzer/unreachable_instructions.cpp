/*******************************************************************\

Module: List all unreachable instructions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// List all unreachable instructions

#include "unreachable_instructions.h"

#include <util/file_util.h>
#include <util/json_expr.h>
#include <util/options.h>
#include <util/xml.h>

#include <goto-programs/compute_called_functions.h>

#include <analyses/ai.h>
#include <analyses/cfg_dominators.h>

typedef std::map<unsigned, goto_programt::const_targett> dead_mapt;

static void unreachable_instructions(
  const goto_programt &goto_program,
  dead_mapt &dest)
{
  cfg_dominatorst dominators;
  dominators(goto_program);

  for(cfg_dominatorst::cfgt::entry_mapt::const_iterator
      it=dominators.cfg.entry_map.begin();
      it!=dominators.cfg.entry_map.end();
      ++it)
  {
    const cfg_dominatorst::cfgt::nodet &n=dominators.cfg[it->second];
    if(n.dominators.empty())
      dest.insert(std::make_pair(it->first->location_number,
                                 it->first));
  }
}

static void all_unreachable(
  const goto_programt &goto_program,
  dead_mapt &dest)
{
  forall_goto_program_instructions(it, goto_program)
    if(!it->is_end_function())
      dest.insert(std::make_pair(it->location_number, it));
}

static void build_dead_map_from_ai(
  const goto_programt &goto_program,
  const ai_baset &ai,
  dead_mapt &dest)
{
  forall_goto_program_instructions(it, goto_program)
    if(ai.abstract_state_before(it)->is_bottom())
      dest.insert(std::make_pair(it->location_number, it));
}

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
    goto_program.output_instruction(ns, "", os, *it->second);
}

static void add_to_xml(
  const goto_programt &goto_program,
  const dead_mapt &dead_map,
  xmlt &dest)
{
  PRECONDITION(!goto_program.instructions.empty());
  goto_programt::const_targett end_function=
    goto_program.instructions.end();
  --end_function;
  DATA_INVARIANT(end_function->is_end_function(),
                 "The last instruction in a goto-program must be END_FUNCTION");

  xmlt &x = dest.new_element("function");
  x.set_attribute("name", id2string(end_function->function));

  for(dead_mapt::const_iterator it=dead_map.begin();
      it!=dead_map.end();
      ++it)
  {
    xmlt &inst = x.new_element("instruction");
    inst.set_attribute("location_number",
                       std::to_string(it->second->location_number));
    inst.set_attribute("source_location",
                       it->second->source_location.as_string());
  }
  return;
}

static void add_to_json(
  const namespacet &ns,
  const goto_programt &goto_program,
  const dead_mapt &dead_map,
  json_arrayt &dest)
{
  json_objectt &entry=dest.push_back().make_object();

  PRECONDITION(!goto_program.instructions.empty());
  goto_programt::const_targett end_function=
    goto_program.instructions.end();
  --end_function;
  DATA_INVARIANT(end_function->is_end_function(),
                 "The last instruction in a goto-program must be END_FUNCTION");

  entry["function"] = json_stringt(end_function->function);
  entry["fileName"]=
    json_stringt(concat_dir_file(
        id2string(end_function->source_location.get_working_directory()),
        id2string(end_function->source_location.get_file())));

  json_arrayt &dead_ins=entry["unreachableInstructions"].make_array();

  for(dead_mapt::const_iterator it=dead_map.begin();
      it!=dead_map.end();
      ++it)
  {
    std::ostringstream oss;
    goto_program.output_instruction(ns, "", oss, *it->second);
    std::string s=oss.str();

    std::string::size_type n=s.find('\n');
    assert(n!=std::string::npos);
    s.erase(0, n+1);
    n=s.find_first_not_of(' ');
    assert(n!=std::string::npos);
    s.erase(0, n);
    assert(!s.empty());
    s.erase(s.size()-1);

    // print info for file actually with full path
    json_objectt &i_entry=dead_ins.push_back().make_object();
    const source_locationt &l=it->second->source_location;
    i_entry["sourceLocation"]=json(l);
    i_entry["statement"]=json_stringt(s);
  }
}

void unreachable_instructions(
  const goto_modelt &goto_model,
  const bool json,
  std::ostream &os)
{
  json_arrayt json_result;

  std::unordered_set<irep_idt> called = compute_called_functions(goto_model);

  const namespacet ns(goto_model.symbol_table);

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available())
      continue;

    const goto_programt &goto_program=f_it->second.body;
    dead_mapt dead_map;

    const symbolt &decl=ns.lookup(f_it->first);

    // f_it->first may be a link-time renamed version, use the
    // base_name instead; do not list inlined functions
    if(called.find(decl.base_name)!=called.end() ||
       f_it->second.is_inlined())
      unreachable_instructions(goto_program, dead_map);
    else
      all_unreachable(goto_program, dead_map);

    if(!dead_map.empty())
    {
      if(!json)
        output_dead_plain(ns, goto_program, dead_map, os);
      else
        add_to_json(ns, goto_program, dead_map, json_result);
    }
  }

  if(json && !json_result.array.empty())
    os << json_result << '\n';
}

bool static_unreachable_instructions(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  const optionst &options,
  std::ostream &out)
{
  json_arrayt json_result;
  xmlt xml_result("unreachable-instructions");

  const namespacet ns(goto_model.symbol_table);

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available())
      continue;

    const goto_programt &goto_program=f_it->second.body;
    dead_mapt dead_map;
    build_dead_map_from_ai(goto_program, ai, dead_map);

    if(!dead_map.empty())
    {
      if(options.get_bool_option("json"))
      {
        add_to_json(ns, f_it->second.body, dead_map, json_result);
      }
      else if(options.get_bool_option("xml"))
      {
        add_to_xml(f_it->second.body, dead_map, xml_result);
      }
      else
      {
        // text or console
        output_dead_plain(ns, f_it->second.body, dead_map, out);
      }
    }
  }

  if(options.get_bool_option("json") && !json_result.array.empty())
    out << json_result << '\n';
  else if(options.get_bool_option("xml"))
    out << xml_result << '\n';

  return false;
}



static void json_output_function(
  const irep_idt &function,
  const source_locationt &first_location,
  const source_locationt &last_location,
  json_arrayt &dest)
{
  json_objectt &entry=dest.push_back().make_object();

  entry["function"] = json_stringt(function);
  entry["file name"]=
    json_stringt(concat_dir_file(
        id2string(first_location.get_working_directory()),
        id2string(first_location.get_file())));
  entry["first line"]=
    json_numbert(id2string(first_location.get_line()));
  entry["last line"]=
    json_numbert(id2string(last_location.get_line()));
}

static void xml_output_function(
  const irep_idt &function,
  const source_locationt &first_location,
  const source_locationt &last_location,
  xmlt &dest)
{
  xmlt &x=dest.new_element("function");

  x.set_attribute("name", id2string(function));
  x.set_attribute("file name",
                  concat_dir_file(
                    id2string(first_location.get_working_directory()),
                    id2string(first_location.get_file())));
  x.set_attribute("first line", id2string(first_location.get_line()));
  x.set_attribute("last line", id2string(last_location.get_line()));
}

static void list_functions(
  const goto_modelt &goto_model,
  const std::unordered_set<irep_idt> &called,
  const optionst &options,
  std::ostream &os,
  bool unreachable)
{
  json_arrayt json_result;
  xmlt xml_result(unreachable ?
                  "unreachable-functions" :
                  "reachable-functions");

  const namespacet ns(goto_model.symbol_table);

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    const symbolt &decl=ns.lookup(f_it->first);

    // f_it->first may be a link-time renamed version, use the
    // base_name instead; do not list inlined functions
    if(unreachable ==
       (called.find(decl.base_name)!=called.end() ||
        f_it->second.is_inlined()))
      continue;

    source_locationt first_location=decl.location;

    source_locationt last_location;
    if(f_it->second.body_available())
    {
      const goto_programt &goto_program=f_it->second.body;

      goto_programt::const_targett end_function=
        goto_program.instructions.end();

      // find the last instruction with a line number
      // TODO(tautschnig): #918 will eventually ensure that every instruction
      // has such
      do
      {
        --end_function;
        last_location = end_function->source_location;
      }
      while(
        end_function != goto_program.instructions.begin() &&
        last_location.get_line().empty());

      if(last_location.get_line().empty())
        last_location = decl.location;
    }
    else
      // completely ignore functions without a body, both for
      // reachable and unreachable functions; we could also restrict
      // this to macros/asm renaming
      continue;

    if(options.get_bool_option("json"))
    {
      json_output_function(
        decl.base_name,
        first_location,
        last_location,
        json_result);
    }
    else if(options.get_bool_option("xml"))
    {
      xml_output_function(
        decl.base_name,
        first_location,
        last_location,
        xml_result);
    }
    else
    {
      // text or console
      os << concat_dir_file(
              id2string(first_location.get_working_directory()),
              id2string(first_location.get_file())) << " "
         << decl.base_name << " "
         << first_location.get_line() << " "
         << last_location.get_line() << "\n";
    }
  }

  if(options.get_bool_option("json") && !json_result.array.empty())
    os << json_result << '\n';
  else if(options.get_bool_option("xml"))
    os << xml_result << '\n';
}

void unreachable_functions(
  const goto_modelt &goto_model,
  const bool json,
  std::ostream &os)
{
  optionst options;
  if(json)
    options.set_option("json", true);

  std::unordered_set<irep_idt> called = compute_called_functions(goto_model);

  list_functions(goto_model, called, options, os, true);
}

void reachable_functions(
  const goto_modelt &goto_model,
  const bool json,
  std::ostream &os)
{
  optionst options;
  if(json)
    options.set_option("json", true);

  std::unordered_set<irep_idt> called = compute_called_functions(goto_model);

  list_functions(goto_model, called, options, os, false);
}

std::unordered_set<irep_idt> compute_called_functions_from_ai(
  const goto_modelt &goto_model,
  const ai_baset &ai)
{
  std::unordered_set<irep_idt> called;

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available())
      continue;

    const goto_programt &p = f_it->second.body;

    if(!ai.abstract_state_before(p.instructions.begin())->is_bottom())
      called.insert(f_it->first);
  }

  return called;
}

bool static_unreachable_functions(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  const optionst &options,
  std::ostream &out)
{
  std::unordered_set<irep_idt> called =
    compute_called_functions_from_ai(goto_model, ai);

  list_functions(goto_model, called, options, out, true);

  return false;
}

bool static_reachable_functions(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  const optionst &options,
  std::ostream &out)
{
  std::unordered_set<irep_idt> called =
    compute_called_functions_from_ai(goto_model, ai);

  list_functions(goto_model, called, options, out, false);

  return false;
}
