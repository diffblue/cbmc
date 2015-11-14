#include <algorithm>

#include <util/bv_arithmetic.h>

#include <goto-programs/goto_trace.h>
#include <goto-programs/goto_functions.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/value/danger_goto_solution.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/util/copy_instructions.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/symex/learn/instruction_set_factory.h>
#include <cegis/danger/symex/learn/replace_operators.h>
#include <cegis/danger/symex/learn/solution_factory.h>
#include <cegis/danger/symex/learn/read_x0.h>

namespace
{
const size_t get_const_value(const exprt &expr)
{
  const bv_arithmetict bv(expr);
  return bv.to_integer().to_ulong();
}

typedef std::map<size_t, const irep_idt> danger_variable_namest;

void reverse(danger_variable_namest &names, const danger_variable_idst &o)
{
  for (danger_variable_idst::const_iterator it=o.begin(); it != o.end(); ++it)
    names.insert(std::make_pair(it->second, it->first));
}

size_t create_temps(danger_variable_namest &rnames, const size_t num_tmp)
{
  for (size_t i=0; i < num_tmp; ++i)
    rnames.insert(std::make_pair(i, get_danger_meta_name(get_tmp(i))));
  return num_tmp;
}

typedef enum
{
  INV, RNK, SKO
} prog_typet;

goto_programt::instructionst &get_prog(
    danger_goto_solutiont::danger_programst &progs, const prog_typet type,
    const size_t instr_idx)
{
  switch (type)
  {
  case INV:
    if (!instr_idx) progs.push_back(danger_goto_solutiont::danger_programt());
    return progs.back().invariant;
  case SKO:
    return progs.back().skolem;
  case RNK:
    return progs.back().ranking;
  default:
    return progs.back().invariant;
  }
}

class read_instrt
{
  danger_goto_solutiont::danger_programst &progs;
  const danger_programt &danger_prog;
  const danger_variable_namest &names;
  danger_variable_namest rnames;
  const instruction_sett &instrset;
  const size_t max_size;
  size_t loop_index;
  size_t insidx;
  prog_typet prog_type;

  void switch_prog()
  {
    insidx=0;
    rnames.clear();
    switch (prog_type)
    {
    case INV:
    {
      const size_t idx=create_temps(rnames, max_size - 1);
      const std::string result(get_danger_meta_name(get_Rx(loop_index, 0))); // XXX: Lexicographical ranking?
      rnames.insert(std::make_pair(idx, result));
      prog_type=RNK;
      break;
    }
    case RNK:
    {
      const danger_programt::loopt &loop=danger_prog.loops[loop_index];
      const size_t num_skolem=loop.skolem_choices.size();
      const size_t num_temps=create_temps(rnames, max_size - num_skolem);
      for (size_t i=num_temps; i < max_size; ++i)
      {
        const size_t sk=i - num_temps;
        const std::string name(get_danger_meta_name(get_Sx(loop_index, sk)));
        rnames.insert(std::make_pair(i, name));
      }
      prog_type=SKO;
      ++loop_index;
      break;
    }
    case SKO:
    {
      const size_t idx=create_temps(rnames, max_size - 1);
      const std::string result_name(get_danger_meta_name(get_Dx(loop_index)));
      rnames.insert(std::make_pair(idx, result_name));
      prog_type=INV;
      break;
    }
    }
  }
public:
  read_instrt(danger_goto_solutiont::danger_programst &progs,
      const danger_programt &danger_prog, const danger_variable_namest &names,
      const instruction_sett &instrset, const size_t max_size) :
      progs(progs), danger_prog(danger_prog), names(names), instrset(instrset), max_size(
          max_size), loop_index(0u), insidx(0u), prog_type(SKO)
  {
    switch_prog();
  }

  void operator()(const exprt &prog_arary_member)
  {
    const struct_exprt &instr_rep=to_struct_expr(prog_arary_member);
    const size_t opcode=get_const_value(instr_rep.op0());
    const instruction_sett::const_iterator instr_entry=instrset.find(opcode);
    assert(instrset.end() != instr_entry);
    goto_programt::instructionst &prog=get_prog(progs, prog_type, insidx);
    const goto_programt::instructionst &instr=instr_entry->second;
    goto_programt::targett first=prog.end();
    const goto_programt::targett last=prog.end();
    copy_instructionst copy_instr;
    for (goto_programt::const_targett it=instr.begin(); it != instr.end(); ++it)
    {
      prog.push_back(goto_programt::instructiont());
      goto_programt::targett new_instr=prog.end();
      copy_instr(--new_instr, it);
    }
    copy_instr.finalize();
    std::advance(first, -instr.size());
    const size_t op0=get_const_value(instr_rep.op1());
    const size_t op1=get_const_value(instr_rep.op2());
    const size_t op2=get_const_value(instr_rep.op3());
    const symbol_tablet &st=danger_prog.st;
    replace_ops_in_instr(st, first, last, names, rnames, op0, op1, op2, insidx);
    if (++insidx % max_size == 0)
    {
      danger_make_presentable(prog);
      switch_prog();
    }
  }
};

class read_instrt_reft
{
  read_instrt &ref;
public:
  read_instrt_reft(read_instrt &ref) :
      ref(ref)
  {
  }
  void operator()(const exprt &prog_arary_member)
  {
    ref(prog_arary_member);
  }
};

class extract_programt
{
  read_instrt read_instr;
public:
  extract_programt(danger_goto_solutiont::danger_programst &progs,
      const danger_programt &prog, const danger_variable_namest &names,
      const instruction_sett &instrset, const size_t max_size) :
      read_instr(progs, prog, names, instrset, max_size)
  {
  }

  void operator()(const goto_trace_stept &step)
  {
    if (goto_trace_stept::DECL != step.type) return;
    const exprt &value=step.full_lhs_value;
    if (ID_array != value.id()) return;
    const typet &type=value.type().subtype();
    if (ID_struct != type.id()) return;
    const std::string &tname=id2string(to_struct_type(type).get_tag());
    const char * const danger_tag=&DANGER_INSTRUCTION_TYPE_NAME[4];
    if (std::string::npos == tname.find(danger_tag)) return;
    const exprt::operandst &instructions=value.operands();
    read_instrt_reft read_instr(this->read_instr);
    std::for_each(instructions.begin(), instructions.end(), read_instr);
  }
};

void extract_programs(danger_goto_solutiont::danger_programst &progs,
    const danger_programt &prog, const goto_tracet &trace,
    const danger_variable_namest &names, const instruction_sett &instrset,
    const size_t max_size)
{
  const extract_programt extract(progs, prog, names, instrset, max_size);
  std::for_each(trace.steps.begin(), trace.steps.end(), extract);
}
}

void create_danger_solution(danger_goto_solutiont &result,
    const danger_programt &prog, const goto_tracet &trace,
    const danger_variable_idst &ids, const size_t max_size)
{
  typedef std::map<size_t, const irep_idt> danger_variable_namest;
  danger_variable_namest names;
  reverse(names, ids);
  instruction_sett instr_set;
  extract_instruction_set(instr_set, prog.gf);
  danger_goto_solutiont::danger_programst &progs=result.danger_programs;
  extract_programs(progs, prog, trace, names, instr_set, max_size);
  danger_read_x0(result, prog, trace);
}
