/*******************************************************************\

Module: List all unreachable instructions

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// List all unreachable instructions

#include "unreachable_instructions.h"

#include <util/json_irep.h>
#include <util/options.h>
#include <util/xml.h>

#include <goto-programs/compute_called_functions.h>

#include <analyses/ai.h>
#include <analyses/cfg_dominators.h>

#include <filesystem>

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
  const irep_idt &function_identifier,
  const goto_programt &goto_program,
  const dead_mapt &dead_map,
  std::ostream &os)
{
  os << "\n*** " << function_identifier << " ***\n";

  for(dead_mapt::const_iterator it=dead_map.begin();
      it!=dead_map.end();
      ++it)
    it->second->output(os);
}

static void add_to_xml(
  const irep_idt &function_identifier,
  const goto_programt &goto_program,
  const dead_mapt &dead_map,
  xmlt &dest)
{
  xmlt &x = dest.new_element("function");
  x.set_attribute("name", id2string(function_identifier));

  for(dead_mapt::const_iterator it=dead_map.begin();
      it!=dead_map.end();
      ++it)
  {
    xmlt &inst = x.new_element("instruction");
    inst.set_attribute("location_number",
                       std::to_string(it->second->location_number));
    inst.set_attribute(
      "source_location", it->second->source_location().as_string());
  }
  return;
}

static optionalt<std::string>
file_name_string_opt(const source_locationt &source_location)
{
  if(source_location.get_file().empty())
    return {};

  return std::filesystem::path(
           id2string(source_location.get_working_directory()))
    .append(id2string(source_location.get_file()))
    .string();
}

static void add_to_json(
  const namespacet &ns,
  const irep_idt &function_identifier,
  const goto_programt &goto_program,
  const dead_mapt &dead_map,
  json_arrayt &dest)
{
  PRECONDITION(!goto_program.instructions.empty());
  goto_programt::const_targett end_function=
    goto_program.instructions.end();
  --end_function;
  DATA_INVARIANT(end_function->is_end_function(),
                 "The last instruction in a goto-program must be END_FUNCTION");

  json_objectt entry{{"function", json_stringt(function_identifier)}};
  if(auto file_name_opt = file_name_string_opt(end_function->source_location()))
    entry["file"] = json_stringt{*file_name_opt};

  json_arrayt &dead_ins=entry["unreachableInstructions"].make_array();

  for(dead_mapt::const_iterator it=dead_map.begin();
      it!=dead_map.end();
      ++it)
  {
    std::ostringstream oss;
    it->second->output(oss);
    std::string s=oss.str();

    std::string::size_type n=s.find('\n');
    CHECK_RETURN(n != std::string::npos);
    s.erase(0, n+1);
    n=s.find_first_not_of(' ');
    CHECK_RETURN(n != std::string::npos);
    s.erase(0, n);
    CHECK_RETURN(!s.empty());
    s.erase(s.size()-1);

    // print info for file actually with full path
    const source_locationt &l = it->second->source_location();
    json_objectt i_entry{{"sourceLocation", json(l)},
                         {"statement", json_stringt(s)}};
    dead_ins.push_back(std::move(i_entry));
  }

  dest.push_back(std::move(entry));
}

void unreachable_instructions(
  const goto_modelt &goto_model,
  const bool json,
  std::ostream &os)
{
  json_arrayt json_result;

  std::unordered_set<irep_idt> called = compute_called_functions(goto_model);

  const namespacet ns(goto_model.symbol_table);

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(!gf_entry.second.body_available())
      continue;

    const goto_programt &goto_program = gf_entry.second.body;
    dead_mapt dead_map;

    const symbolt &decl = ns.lookup(gf_entry.first);

    if(
      called.find(decl.name) != called.end() ||
      to_code_type(decl.type).get_inlined())
    {
      unreachable_instructions(goto_program, dead_map);
    }
    else
      all_unreachable(goto_program, dead_map);

    if(!dead_map.empty())
    {
      if(!json)
        output_dead_plain(ns, gf_entry.first, goto_program, dead_map, os);
      else
        add_to_json(ns, gf_entry.first, goto_program, dead_map, json_result);
    }
  }

  if(json && !json_result.empty())
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

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(!gf_entry.second.body_available())
      continue;

    const goto_programt &goto_program = gf_entry.second.body;
    dead_mapt dead_map;
    build_dead_map_from_ai(goto_program, ai, dead_map);

    if(!dead_map.empty())
    {
      if(options.get_bool_option("json"))
      {
        add_to_json(
          ns, gf_entry.first, gf_entry.second.body, dead_map, json_result);
      }
      else if(options.get_bool_option("xml"))
      {
        add_to_xml(gf_entry.first, gf_entry.second.body, dead_map, xml_result);
      }
      else
      {
        // text or console
        output_dead_plain(
          ns, gf_entry.first, gf_entry.second.body, dead_map, out);
      }
    }
  }

  if(options.get_bool_option("json") && !json_result.empty())
    out << json_result << '\n';
  else if(options.get_bool_option("xml"))
    out << xml_result << '\n';

  return false;
}

static optionalt<std::string>
line_string_opt(const source_locationt &source_location)
{
  const irep_idt &line = source_location.get_line();

  if(line.empty())
    return {};
  else
    return id2string(line);
}

static void json_output_function(
  const irep_idt &function,
  const source_locationt &first_location,
  const source_locationt &last_location,
  json_arrayt &dest)
{
  json_objectt entry{{"function", json_stringt(function)}};
  if(auto file_name_opt = file_name_string_opt(first_location))
    entry["file"] = json_stringt{*file_name_opt};
  if(auto line_opt = line_string_opt(first_location))
    entry["firstLine"] = json_numbert{*line_opt};
  if(auto line_opt = line_string_opt(last_location))
    entry["lastLine"] = json_numbert{*line_opt};

  dest.push_back(std::move(entry));
}

static void xml_output_function(
  const irep_idt &function,
  const source_locationt &first_location,
  const source_locationt &last_location,
  xmlt &dest)
{
  xmlt &x=dest.new_element("function");

  x.set_attribute("name", id2string(function));
  if(auto file_name_opt = file_name_string_opt(first_location))
    x.set_attribute("file", *file_name_opt);
  if(auto line_opt = line_string_opt(first_location))
    x.set_attribute("first_line", *line_opt);
  if(auto line_opt = line_string_opt(last_location))
    x.set_attribute("last_line", *line_opt);
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

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    const symbolt &decl = ns.lookup(gf_entry.first);

    if(
      unreachable == (called.find(decl.name) != called.end() ||
                      to_code_type(decl.type).get_inlined()))
    {
      continue;
    }

    source_locationt first_location=decl.location;

    source_locationt last_location;
    if(gf_entry.second.body_available())
    {
      const goto_programt &goto_program = gf_entry.second.body;

      goto_programt::const_targett end_function=
        goto_program.instructions.end();

      // find the last instruction with a line number
      // TODO(tautschnig): #918 will eventually ensure that every instruction
      // has such
      do
      {
        --end_function;
        last_location = end_function->source_location();
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
      if(auto file_name_opt = file_name_string_opt(first_location))
        os << *file_name_opt << ' ';
      os << decl.base_name;
      if(auto line_opt = line_string_opt(first_location))
        os << ' ' << *line_opt;
      if(auto line_opt = line_string_opt(last_location))
        os << ' ' << *line_opt;
      os << '\n';
    }
  }

  if(options.get_bool_option("json") && !json_result.empty())
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

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(!gf_entry.second.body_available())
      continue;

    const goto_programt &p = gf_entry.second.body;

    if(!ai.abstract_state_before(p.instructions.begin())->is_bottom())
      called.insert(gf_entry.first);
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
