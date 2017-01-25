/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <goto-programs/goto_trace.h>
#include <goto-programs/goto_functions.h>

#include <cegis/value/program_individual_serialisation.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instructions/instruction_set_factory.h>
#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/symex/learn/replace_operators.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/value/danger_goto_solution.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/symex/learn/solution_factory.h>
#include <cegis/danger/symex/learn/read_x0.h>

namespace
{
size_t create_temps(invariant_variable_namest &rnames, const size_t num_tmp)
{
  for (size_t i=0; i < num_tmp; ++i)
    rnames.insert(std::make_pair(i, get_cegis_meta_name(get_tmp(i))));
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

// TODO: Replace construct by name prefixes for programs
class read_instrt
{
  danger_goto_solutiont::danger_programst &progs;
  const danger_programt &danger_prog;
  const invariant_variable_namest &names;
  invariant_variable_namest rnames;
  const instruction_sett &instrset;
  size_t prog_size;
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
      if (prog_size)
      {
        const size_t idx=create_temps(rnames, prog_size - 1);
        const std::string result(get_cegis_meta_name(get_Rx(loop_index, 0))); // XXX: Lexicographical ranking?
        rnames.insert(std::make_pair(idx, result));
      }
      prog_type=RNK;
      break;
    }
    case RNK:
    {
      const danger_programt::loopt &loop=danger_prog.loops[loop_index];
      const size_t num_skolem=loop.skolem_choices.size();
      const size_t num_temps=create_temps(rnames, prog_size - num_skolem);
      for (size_t i=num_temps; i < prog_size; ++i)
      {
        const size_t sk=i - num_temps;
        const std::string name(get_cegis_meta_name(get_Sx(loop_index, sk)));
        rnames.insert(std::make_pair(i, name));
      }
      prog_type=SKO;
      ++loop_index;
      break;
    }
    case SKO:
    {
      const size_t idx=create_temps(rnames, prog_size - 1);
      const std::string result_name(
          get_cegis_meta_name(get_Dx(loop_index)));
      rnames.insert(std::make_pair(idx, result_name));
      prog_type=INV;
      break;
    }
    }
  }
public:
  read_instrt(danger_goto_solutiont::danger_programst &progs,
      const danger_programt &danger_prog, const invariant_variable_namest &names,
      const instruction_sett &instrset, const size_t prog_size) :
      progs(progs), danger_prog(danger_prog), names(names), instrset(instrset), prog_size(
          prog_size), loop_index(0u), insidx(0u), prog_type(SKO)
  {
    switch_prog();
  }

  read_instrt(danger_goto_solutiont::danger_programst &progs,
      const danger_programt &danger_prog, const invariant_variable_namest &names,
      const instruction_sett &instrset) :
      progs(progs), danger_prog(danger_prog), names(names), instrset(instrset), prog_size(
          0u), loop_index(0u), insidx(0u), prog_type(SKO)
  {
  }

  void operator()(const program_individualt::instructiont &instruction)
  {
    const program_individualt::instructiont::opcodet opcode=instruction.opcode;
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
    const program_individualt::instructiont::opst &ops=instruction.ops;
    const size_t empty_op=0u;
    const size_t op0=!ops.empty() ? ops.front() : empty_op;
    const size_t op1=ops.size() >= 2 ? ops.at(1) : empty_op;
    const size_t op2=ops.size() >= 3 ? ops.at(2) : empty_op;
    const symbol_tablet &st=danger_prog.st;
    replace_ops_in_instr(st, DANGER_EXECUTE, first, last, names, rnames, op0,
        op1, op2, insidx);
    if (++insidx % prog_size == 0) invariant_make_presentable(prog);
  }

  void operator()(const exprt &prog_arary_member)
  {
    const struct_exprt &instr_rep=to_struct_expr(prog_arary_member);
    operator()(to_program_individual_instruction(instr_rep));
    if (insidx % prog_size == 0) switch_prog();
  }

  void set_prog_size(const size_t prog_size)
  {
    this->prog_size=prog_size;
    switch_prog();
  }
};

class extract_programt
{
  read_instrt read_instr;
public:
  extract_programt(danger_goto_solutiont::danger_programst &progs,
      const danger_programt &prog, const invariant_variable_namest &names,
      const instruction_sett &instrset, const size_t max_size) :
      read_instr(progs, prog, names, instrset, max_size)
  {
  }

  void operator()(const goto_trace_stept &step)
  {
    if (!is_program_individual_decl(step)) return;
    for (const exprt &prog_array_member : step.full_lhs_value.operands())
      read_instr(prog_array_member);
  }
};

void extract_programs(danger_goto_solutiont::danger_programst &progs,
    const danger_programt &prog, const goto_tracet &trace,
    const invariant_variable_namest &names, const instruction_sett &instrset,
    const size_t max_size)
{
  const extract_programt extract(progs, prog, names, instrset, max_size);
  std::for_each(trace.steps.begin(), trace.steps.end(), extract);
}

void extract_instruction_set(instruction_sett &instr_set,
    const goto_functionst &gf)
{
  typedef goto_functionst::function_mapt function_mapt;
  const function_mapt &function_map=gf.function_map;
  const function_mapt::const_iterator it=function_map.find(DANGER_EXECUTE);
  assert(function_map.end() != it);
  instr_set=extract_instruction_set(it->second.body);
}
}

void create_danger_solution(danger_goto_solutiont &result,
    const danger_programt &prog, const goto_tracet &trace,
    const operand_variable_idst &ids, const size_t max_size)
{
  invariant_variable_namest names;
  reverse_invariant_var_ids(names, ids);
  instruction_sett instr_set;
  extract_instruction_set(instr_set, prog.gf);
  danger_goto_solutiont::danger_programst &progs=result.danger_programs;
  extract_programs(progs, prog, trace, names, instr_set, max_size);
  danger_read_x0(result, prog, trace);
}

void create_danger_solution(danger_goto_solutiont &result,
    const danger_programt &prog, const program_individualt &ind,
    const instruction_sett &instr_set, const operand_variable_idst &ids)
{
  invariant_variable_namest names;
  reverse_invariant_var_ids(names, ids);
  danger_goto_solutiont::danger_programst &progs=result.danger_programs;
  progs.clear();
  typedef program_individualt individualt;
  const individualt::programst &ind_progs=ind.programs;
  read_instrt extract(progs, prog, names, instr_set);
  for (const individualt::programt &program : ind_progs)
  {
    extract.set_prog_size(program.size());
    for (const individualt::instructiont &instr : program)
      extract(instr);
  }
  danger_goto_solutiont::nondet_choicest &nondet=result.x0_choices;
  nondet.clear();
  const typet type=cegis_default_integer_type(); // XXX: Currently single data type.
  for (const individualt::x0t::value_type &x0 : ind.x0)
    nondet.push_back(from_integer(x0, type));
}

void create_danger_solution(danger_goto_solutiont &result,
    const danger_programt &prog, const program_individualt &ind,
    const operand_variable_idst &ids)
{
  instruction_sett instr_set;
  extract_instruction_set(instr_set, prog.gf);
  create_danger_solution(result, prog, ind, instr_set, ids);
}
