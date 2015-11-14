#include <algorithm>
#include <cstring>

#include <goto-programs/goto_functions.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/util/copy_instructions.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/symex/learn/instruction_set_factory.h>

namespace
{
const char FIRST_PREFIX[]="__CPROVER_danger_opcode_first_";
const char LAST_PREFIX[]="__CPROVER_danger_opcode_last_";
const char SINGLE_PREFIX[]="__CPROVER_danger_opcode_";

class execute_instruction_handlert
{
  copy_instructionst copy_instruction;
  instruction_sett &instruction_set;
  bool has_current_instr;
  bool is_last_in_range;
  size_t instr_idx;
  goto_programt::const_targett current_instr_offset;
public:
  execute_instruction_handlert(instruction_sett &instruction_set) :
      instruction_set(instruction_set), has_current_instr(false), is_last_in_range(
          false), instr_idx(0u)
  {
  }

  void handle_meta_info(const goto_programt::const_targett &target)
  {
    const goto_programt::instructiont &instr=*target;
    const goto_programt::instructiont::labelst &labels=instr.labels;
    if (labels.empty()) return;
    const std::string &label=id2string(instr.labels.front());
    if (std::string::npos != label.find(FIRST_PREFIX))
    {
      current_instr_offset=target;
      has_current_instr=true;
      is_last_in_range=false;
      instr_idx=string2integer(label.substr(strlen(FIRST_PREFIX))).to_ulong();
    } else if (std::string::npos != label.find(LAST_PREFIX))
    {
      is_last_in_range=true;
      instr_idx=string2integer(label.substr(strlen(LAST_PREFIX))).to_ulong();
    } else if (std::string::npos != label.find(SINGLE_PREFIX))
    {
      has_current_instr=true;
      is_last_in_range=true;
      instr_idx=string2integer(label.substr(strlen(SINGLE_PREFIX))).to_ulong();
    }
  }

  void copy_op(goto_programt::const_targett target)
  {
    goto_programt::instructionst &instr=instruction_set[instr_idx];
    instr.push_back(goto_programt::instructiont());
    goto_programt::targett new_target=instr.end();
    copy_instruction(--new_target, target);
    if (is_last_in_range)
    {
      instr.push_back(goto_programt::instructiont(SKIP));
      goto_programt::targett new_target=instr.end();
      copy_instruction.finalize(--new_target, ++target);
      has_current_instr=false;
    }
  }

  void operator()(const goto_programt::const_targett &target)
  {
    handle_meta_info(target);
    if (has_current_instr) copy_op(target);
  }
};
}

void extract_instruction_set(instruction_sett &instruction_set,
    const goto_functionst &gf)
{
  typedef goto_functionst::function_mapt function_mapt;
  const function_mapt &function_map=gf.function_map;
  const function_mapt::const_iterator it=function_map.find(DANGER_EXECUTE);
  assert(function_map.end() != it);
  const goto_programt::instructionst &body=it->second.body.instructions;
  execute_instruction_handlert handler(instruction_set);
  for (goto_programt::const_targett it=body.begin(); it != body.end(); ++it)
    handler(it);
}
