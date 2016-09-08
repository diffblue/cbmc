#include <util/cprover_prefix.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/cegis-util/counterexample_vars.h>

void collect_counterexample_locations(goto_programt::targetst &locs,
    const char * const marker_prefix, goto_programt &prog,
    const std::function<bool(goto_programt::const_targett target)> is_meta)
{
  goto_programt::instructionst &body=prog.instructions;
  const goto_programt::targett end(body.end());
  size_t marker_index=0;
  for (goto_programt::targett instr=body.begin(); instr != end; ++instr)
    if (is_nondet(instr, end) && !is_meta(instr))
    {
      assert(instr->labels.empty());
      instr->labels.push_back(marker_prefix + std::to_string(marker_index++));
      locs.push_back(instr);
    }
}

namespace
{
bool is_meta(const goto_programt::const_targett pos)
{
  const goto_programt::instructiont &instr=*pos;
  const goto_program_instruction_typet type=instr.type;
  if (goto_program_instruction_typet::ASSIGN == type
      && ID_symbol != to_code_assign(instr.code).rhs().id()) return false;
  const std::string &name=id2string(get_affected_variable(instr));
  return contains(name, CPROVER_PREFIX) || is_return_value_name(name);
}
}

void collect_counterexample_locations(goto_programt::targetst &locs,
    const char * const marker_prefix, goto_programt &prog)
{
  collect_counterexample_locations(locs, marker_prefix, prog, is_meta);
}

void collect_counterexample_locations(goto_programt::targetst &locs,
    goto_programt &prog)
{
  collect_counterexample_locations(locs, DEFAULT_MARKER_LABEL_PREFIX, prog);
}
