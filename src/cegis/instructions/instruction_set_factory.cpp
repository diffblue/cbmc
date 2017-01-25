/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <cstring>

#include <goto-programs/goto_functions.h>

#include <cegis/instrument/literals.h>
#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/instructions/instruction_set_factory.h>

namespace
{
class execute_instruction_handlert
{
  const std::string first_prefix;
  const std::string last_prefix;
  const std::string single_prefix;
  copy_instructionst copy_instruction;
  instruction_sett &instruction_set;
  bool has_current_instr;
  bool is_last_in_range;
  size_t instr_idx;
  goto_programt::const_targett current_instr_offset;
public:
  execute_instruction_handlert(const std::string &first_prefix,
      const std::string &last_prefix, const std::string &single_prefix,
      instruction_sett &instruction_set) :
      first_prefix(first_prefix), last_prefix(last_prefix), single_prefix(
          single_prefix), instruction_set(instruction_set), has_current_instr(
          false), is_last_in_range(false), instr_idx(0u)
  {
  }

  void handle_meta_info(const goto_programt::const_targett &target)
  {
    const goto_programt::instructiont &instr=*target;
    const goto_programt::instructiont::labelst &labels=instr.labels;
    if (labels.empty()) return;
    const std::string &label=id2string(instr.labels.front());
    if (std::string::npos != label.find(first_prefix))
    {
      current_instr_offset=target;
      has_current_instr=true;
      is_last_in_range=false;
      instr_idx=string2integer(label.substr(first_prefix.size())).to_ulong();
    } else if (std::string::npos != label.find(last_prefix))
    {
      is_last_in_range=true;
      instr_idx=string2integer(label.substr(last_prefix.size())).to_ulong();
    } else if (std::string::npos != label.find(single_prefix))
    {
      has_current_instr=true;
      is_last_in_range=true;
      instr_idx=string2integer(label.substr(single_prefix.size())).to_ulong();
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

#define DEFAULT_FIRST CEGIS_PREFIX "opcode_first_"
#define DEFAULT_LAST CEGIS_PREFIX "opcode_last_"
#define DEFAULT_SINGLE CEGIS_PREFIX "opcode_"

instruction_sett extract_instruction_set(const goto_programt &body)
{
  return extract_instruction_set(body, DEFAULT_FIRST, DEFAULT_LAST, DEFAULT_SINGLE);
}

instruction_sett extract_instruction_set(const goto_programt &body,
    const std::string &first_prefix, const std::string &last_prefix,
    const std::string &single_prefix)
{
  const goto_programt::instructionst &instrs=body.instructions;
  instruction_sett instruction_set;
  execute_instruction_handlert handler(first_prefix, last_prefix, single_prefix, instruction_set);
  for (goto_programt::const_targett it=instrs.begin(); it != instrs.end(); ++it)
    handler(it);
  return instruction_set;
}
