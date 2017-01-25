/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <iostream>

#include <util/cprover_prefix.h>
#include <goto-programs/goto_trace.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/counterexample_vars.h>

namespace
{
size_t collect_counterexample_locations(goto_programt::targetst &locs,
    const char * const marker_prefix, goto_programt &prog,
    const std::function<bool(goto_programt::const_targett target)> is_meta,
    size_t marker_index)
{
  goto_programt::instructionst &body=prog.instructions;
  const goto_programt::targett end(body.end());
  for (goto_programt::targett instr=body.begin(); instr != end; ++instr)
    if (is_nondet(instr, end) && !is_meta(instr))
    {
      assert(instr->labels.empty());
      instr->labels.push_back(marker_prefix + std::to_string(marker_index++));
      locs.push_back(instr);
    }
  return marker_index;
}
}

void collect_counterexample_locations(goto_programt::targetst &locs,
    const char * const marker_prefix, goto_programt &prog,
    const std::function<bool(goto_programt::const_targett target)> is_meta)
{
  collect_counterexample_locations(locs, marker_prefix, prog, is_meta, 0);
}

#define TMP_IF_EXPR_PREFIX "tmp_if_expr$"

bool default_cegis_meta_criterion(const goto_programt::const_targett pos)
{
  const goto_programt::instructiont &instr=*pos;
  const goto_program_instruction_typet type=instr.type;
  if (goto_program_instruction_typet::ASSIGN == type
      && ID_symbol != to_code_assign(instr.code).rhs().id()) return false;
  const std::string &name=id2string(get_affected_variable(instr));
  return contains(name, TMP_IF_EXPR_PREFIX) || contains(name, CPROVER_PREFIX)
      || is_return_value_name(name);
}

void collect_counterexample_locations(goto_programt::targetst &locs,
    const char * const marker_prefix, goto_programt &prog)
{
  collect_counterexample_locations(locs, marker_prefix, prog,
      default_cegis_meta_criterion);
}

void collect_counterexample_locations(goto_programt::targetst &locs,
    goto_programt &prog)
{
  collect_counterexample_locations(locs, DEFAULT_MARKER_LABEL_PREFIX, prog);
}

void collect_counterexample_locations(goto_programt::targetst &locs,
    goto_programt &prog,
    const std::function<bool(goto_programt::const_targett target)> is_meta)
{
  collect_counterexample_locations(locs, DEFAULT_MARKER_LABEL_PREFIX, prog,
      is_meta);
}

size_t collect_counterexample_locations(goto_programt::targetst &locs,
    goto_programt &prog,
    const std::function<bool(goto_programt::const_targett target)> is_meta,
    const size_t marker_index_offset)
{
  return collect_counterexample_locations(locs, DEFAULT_MARKER_LABEL_PREFIX,
      prog, is_meta, marker_index_offset);
}

namespace
{
goto_programt::instructiont::labelst::const_iterator find_ce_label(
    const goto_programt::instructiont::labelst &labels)
{
  const goto_programt::instructiont::labelst::const_iterator end=labels.end();
  return std::find_if(labels.begin(), end,
      [](const irep_idt &label)
      { return std::string::npos != id2string(label).find(DEFAULT_MARKER_LABEL_PREFIX);});
}
}

std::map<const irep_idt, exprt::operandst> extract_counterexample(
    const goto_tracet &trace)
{
  const goto_tracet::stepst &steps=trace.steps;
  std::map<const irep_idt, exprt::operandst> result;
  for (const goto_trace_stept &step : steps)
  {
    typedef goto_programt::instructiont::labelst labelst;
    const labelst &labels=step.pc->labels;
    const labelst::const_iterator it=find_ce_label(labels);
    if (labels.end() == it) continue;
    result[*it].push_back(step.full_lhs_value);
  }
  return result;
}

void show_assignments(std::ostream &os,
    const std::map<const irep_idt, exprt::operandst> &assignments)
{
  for (const std::pair<const irep_idt, exprt::operandst> &ass : assignments)
  {
    os << "<assignment>" << std::endl;
    os << "  <id>" << ass.first << "</id>" << std::endl;
    os << "  <values>" << std::endl;
    for (const exprt &value : ass.second)
      os << "    <value>" << value.pretty() << "</value>" << std::endl;
    os << "  </values>" << std::endl;
    os << "</assignment>" << std::endl;
  }
}

namespace
{
bool is_marker(const irep_idt &label)
{
  return std::string::npos != id2string(label).find(DEFAULT_MARKER_LABEL_PREFIX);
}

typedef goto_programt::instructiont::labelst labelst;
}

bool has_counterexample_marker(const goto_programt::const_targett pos)
{
  const labelst &l=pos->labels;
  return l.end() != std::find_if(l.begin(), l.end(), is_marker);
}

const irep_idt &get_counterexample_marker(
    const goto_programt::const_targett pos)
{
  const labelst &l=pos->labels;
  const labelst::const_iterator it=std::find_if(l.begin(), l.end(), is_marker);
  assert(l.end() != it);
  return *it;
}
