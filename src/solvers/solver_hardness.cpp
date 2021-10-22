/*******************************************************************\

Module: measure and track the complexity of solver queries

Author: Diffblue Ltd.

\*******************************************************************/

#include "solver_hardness.h"

#include <iomanip>

#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/json_irep.h>
#include <util/json_stream.h>
#include <util/std_code.h>

solver_hardnesst::sat_hardnesst &solver_hardnesst::sat_hardnesst::
operator+=(const solver_hardnesst::sat_hardnesst &other)
{
  clauses += other.clauses;
  literals += other.literals;
  variables.insert(other.variables.begin(), other.variables.end());
  clause_set.insert(
    clause_set.end(), other.clause_set.begin(), other.clause_set.end());
  return *this;
}

bool solver_hardnesst::hardness_ssa_keyt::
operator==(const solver_hardnesst::hardness_ssa_keyt &other) const
{
  if(ssa_expression != other.ssa_expression)
    return false;
  return pc->source_location().as_string() ==
         other.pc->source_location().as_string();
}

bool solver_hardnesst::assertion_statst::empty() const
{
  return pcs.empty();
}

void solver_hardnesst::register_ssa(
  std::size_t ssa_index,
  const exprt ssa_expression,
  goto_programt::const_targett pc)
{
  PRECONDITION(ssa_index < hardness_stats.size());

  current_ssa_key.ssa_expression = expr2string(ssa_expression);
  current_ssa_key.pc = pc;
  auto pre_existing =
    hardness_stats[ssa_index].insert({current_ssa_key, current_hardness});
  if(!pre_existing.second)
  { // there already was an element with the same key
    pre_existing.first->second += current_hardness;
  }
  if(hardness_stats[ssa_index].size() > max_ssa_set_size)
    max_ssa_set_size = hardness_stats[ssa_index].size();
  current_ssa_key = {};
  current_hardness = {};
}

void solver_hardnesst::register_ssa_size(std::size_t size)
{
  // do not shrink
  if(size <= hardness_stats.size())
    return;

  hardness_stats.resize(size);
}

void solver_hardnesst::register_assertion_ssas(
  const exprt ssa_expression,
  const std::vector<goto_programt::const_targett> &pcs)
{
  if(assertion_stats.empty())
    return;

  assertion_stats.sat_hardness = current_hardness;
  assertion_stats.ssa_expression = expr2string(ssa_expression);
  assertion_stats.pcs = pcs;
  current_ssa_key = {};
  current_hardness = {};
}

void solver_hardnesst::register_clause(
  const bvt &bv,
  const bvt &cnf,
  const size_t cnf_clause_index,
  bool register_cnf)
{
  current_hardness.clauses++;
  current_hardness.literals += bv.size();

  for(const auto &literal : bv)
  {
    current_hardness.variables.insert(literal.var_no());
  }

  if(register_cnf)
  {
#ifdef DEBUG
    std::cout << cnf_clause_index << ": ";
    for(const auto &literal : cnf)
      std::cout << literal.dimacs() << " ";
    std::cout << "0\n";
#endif
    current_hardness.clause_set.push_back(cnf_clause_index);
  }
}

void solver_hardnesst::set_outfile(const std::string &file_name)
{
  outfile = file_name;
}

void solver_hardnesst::produce_report()
{
  PRECONDITION(!outfile.empty());

  // The SSA steps and indexed internally (by the position in the SSA equation)
  // but if the `--paths` option is used, there are multiple equations, some
  // sharing SSA steps. We only store the unique ones in a set but now we want
  // to identify them by a single number. So we shift the SSA index to make room
  // for the set index.
  std::size_t ssa_set_bit_offset = 0;
  const std::size_t one = 1;
  while((one << ssa_set_bit_offset) < max_ssa_set_size)
    ++ssa_set_bit_offset;

  std::ofstream out{outfile};
  json_stream_arrayt json_stream_array{out};

  for(std::size_t i = 0; i < hardness_stats.size(); i++)
  {
    const auto &ssa_step_hardness = hardness_stats[i];
    if(ssa_step_hardness.empty())
      continue;

    std::size_t j = 0;
    for(const auto &key_value_pair : ssa_step_hardness)
    {
      auto const &ssa = key_value_pair.first;
      auto const &hardness = key_value_pair.second;
      auto hardness_stats_json = json_objectt{};
      hardness_stats_json["SSA_expr"] = json_stringt{ssa.ssa_expression};
      hardness_stats_json["GOTO"] =
        json_stringt{goto_instruction2string(ssa.pc)};

      // It might be desirable to collect all SAT hardness statistics pertaining
      // to a particular GOTO instruction, since there may be a number of SSA
      // steps per GOTO instruction. The following JSON contains a unique
      // identifier for each one.
      hardness_stats_json["GOTO_ID"] =
        json_numbert{std::to_string((i << ssa_set_bit_offset) + j)};
      hardness_stats_json["Source"] = json(ssa.pc->source_location());

      auto sat_hardness_json = json_objectt{};
      sat_hardness_json["Clauses"] =
        json_numbert{std::to_string(hardness.clauses)};
      sat_hardness_json["Literals"] =
        json_numbert{std::to_string(hardness.literals)};
      sat_hardness_json["Variables"] =
        json_numbert{std::to_string(hardness.variables.size())};

      json_arrayt sat_hardness_clause_set_json;
      for(auto const &clause : hardness.clause_set)
      {
        sat_hardness_clause_set_json.push_back(
          json_numbert{std::to_string(clause)});
      }
      sat_hardness_json["ClauseSet"] = sat_hardness_clause_set_json;

      hardness_stats_json["SAT_hardness"] = sat_hardness_json;

      json_stream_array.push_back(hardness_stats_json);
      ++j;
    }
  }

  if(!assertion_stats.empty())
  {
    auto assertion_stats_json = json_objectt{};
    assertion_stats_json["SSA_expr"] =
      json_stringt{assertion_stats.ssa_expression};

    auto assertion_stats_pcs_json = json_arrayt{};
    for(const auto &pc : assertion_stats.pcs)
    {
      auto assertion_stats_pc_json = json_objectt{};
      assertion_stats_pc_json["GOTO"] =
        json_stringt{goto_instruction2string(pc)};
      assertion_stats_pc_json["Source"] = json(pc->source_location());
      assertion_stats_pcs_json.push_back(assertion_stats_pc_json);
    }
    assertion_stats_json["Sources"] = assertion_stats_pcs_json;

    auto assertion_hardness_json = json_objectt{};
    assertion_hardness_json["Clauses"] =
      json_numbert{std::to_string(assertion_stats.sat_hardness.clauses)};
    assertion_hardness_json["Literals"] =
      json_numbert{std::to_string(assertion_stats.sat_hardness.literals)};
    assertion_hardness_json["Variables"] = json_numbert{
      std::to_string(assertion_stats.sat_hardness.variables.size())};

    json_arrayt assertion_sat_hardness_clause_set_json;
    for(auto const &clause : assertion_stats.sat_hardness.clause_set)
    {
      assertion_sat_hardness_clause_set_json.push_back(
        json_numbert{std::to_string(clause)});
    }
    assertion_hardness_json["ClauseSet"] =
      assertion_sat_hardness_clause_set_json;

    assertion_stats_json["SAT_hardness"] = assertion_hardness_json;

    json_stream_array.push_back(assertion_stats_json);
  }
}

std::string
solver_hardnesst::goto_instruction2string(goto_programt::const_targett pc)
{
  std::stringstream out;
  auto instruction = *pc;

  if(!instruction.labels.empty())
  {
    out << "        // Labels:";
    for(const auto &label : instruction.labels)
      out << " " << label;
  }

  if(instruction.is_target())
    out << std::setw(6) << instruction.target_number << ": ";

  switch(instruction.type)
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO INSTRUCTION TYPE SET";
    break;

  case GOTO:
  case INCOMPLETE_GOTO:
    if(!instruction.get_condition().is_true())
    {
      out << "IF " << format(instruction.get_condition()) << " THEN ";
    }

    out << "GOTO ";

    if(instruction.is_incomplete_goto())
    {
      out << "(incomplete)";
    }
    else
    {
      for(auto gt_it = instruction.targets.begin();
          gt_it != instruction.targets.end();
          gt_it++)
      {
        if(gt_it != instruction.targets.begin())
          out << ", ";
        out << (*gt_it)->target_number;
      }
    }
    break;

  case SET_RETURN_VALUE:
    out << "SET RETURN VALUE" << format(instruction.return_value());
    break;

  case OTHER:
  case DECL:
  case DEAD:
  case FUNCTION_CALL:
  case ASSIGN:
    out << format(instruction.get_code());
    break;

  case ASSUME:
  case ASSERT:
    if(instruction.is_assume())
      out << "ASSUME ";
    else
      out << "ASSERT ";

    out << format(instruction.get_condition());
    break;

  case SKIP:
    out << "SKIP";
    break;

  case END_FUNCTION:
    out << "END_FUNCTION";
    break;

  case LOCATION:
    out << "LOCATION";
    break;

  case THROW:
    out << "THROW";

    {
      const irept::subt &exception_list =
        instruction.get_code().find(ID_exception_list).get_sub();

      for(const auto &ex : exception_list)
        out << " " << ex.id();
    }

    if(instruction.get_code().operands().size() == 1)
      out << ": " << format(instruction.get_code().op0());

    break;

  case CATCH:
  {
    if(instruction.get_code().get_statement() == ID_exception_landingpad)
    {
      const auto &landingpad = to_code_landingpad(instruction.get_code());
      out << "EXCEPTION LANDING PAD (" << format(landingpad.catch_expr().type())
          << ' ' << format(landingpad.catch_expr()) << ")";
    }
    else if(instruction.get_code().get_statement() == ID_push_catch)
    {
      out << "CATCH-PUSH ";

      unsigned i = 0;
      const irept::subt &exception_list =
        instruction.get_code().find(ID_exception_list).get_sub();
      DATA_INVARIANT(
        instruction.targets.size() == exception_list.size(),
        "unexpected discrepancy between sizes of instruction"
        "targets and exception list");
      for(auto gt_it = instruction.targets.begin();
          gt_it != instruction.targets.end();
          gt_it++, i++)
      {
        if(gt_it != instruction.targets.begin())
          out << ", ";
        out << exception_list[i].id() << "->" << (*gt_it)->target_number;
      }
    }
    else if(instruction.get_code().get_statement() == ID_pop_catch)
    {
      out << "CATCH-POP";
    }
    else
    {
      UNREACHABLE;
    }
    break;
  }

  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN";
    break;

  case ATOMIC_END:
    out << "ATOMIC_END";
    break;

  case START_THREAD:
    out << "START THREAD " << instruction.get_target()->target_number;
    break;

  case END_THREAD:
    out << "END THREAD";
    break;
  }

  return out.str();
}

std::string solver_hardnesst::expr2string(const exprt expr)
{
  std::stringstream ss;
  ss << format(expr);
  return ss.str();
}
