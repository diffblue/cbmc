#include <util/bv_arithmetic.h>

#include <goto-programs/goto_trace.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>
#include <cegis/danger/symex/learn/read_x0.h>
#include <cegis/danger/symex/learn/solution_factory.h>
#include <cegis/genetic/instruction_set_info_factory.h>
#include <cegis/value/program_individual_serialisation.h>

bool is_program_indivdual_decl(const goto_trace_stept &step)
{
  if (goto_trace_stept::DECL != step.type) return false;
  const exprt &value=step.full_lhs_value;
  if (ID_array != value.id()) return false;
  const typet &type=value.type().subtype();
  if (ID_struct != type.id()) return false;
  const std::string &tname=id2string(to_struct_type(type).get_tag());
  const char * const danger_tag=&DANGER_INSTRUCTION_TYPE_NAME[4];
  return std::string::npos != tname.find(danger_tag);
}

namespace
{
const program_individualt::instructiont::opt get_const_value(const exprt &expr)
{
  const bv_arithmetict bv(expr);
  return static_cast<program_individualt::instructiont::opt>(bv.to_integer().to_ulong());
}
}

program_individualt::instructiont to_program_individual_instruction(
    const struct_exprt &instr_rep)
{
  program_individualt::instructiont result;
  result.opcode=get_const_value(instr_rep.op0());
  result.ops.push_back(get_const_value(instr_rep.op1()));
  result.ops.push_back(get_const_value(instr_rep.op2()));
  result.ops.push_back(get_const_value(instr_rep.op3()));
  return result;
}

program_individualt to_program_individual(const danger_programt &prog,
    const goto_tracet &trace)
{
  program_individualt individual;
  individual.fitness=0u;
  for (const goto_trace_stept &step : trace.steps)
    if (is_program_indivdual_decl(step))
    {
      program_individualt::programt prog;
      for (const exprt &op : step.full_lhs_value.operands())
      {
        const struct_exprt &instr=to_struct_expr(op);
        prog.push_back(to_program_individual_instruction(instr));
      }
      individual.programs.push_back(prog);
    }
  danger_read_x0(individual, prog, trace);
  return individual;
}

#define VALUE "value"

irept singleton_irep(const long long int value)
{
  irept result;
  result.set(VALUE, value);
  return result;
}

long long int get_value(const irept &singleton)
{
  return singleton.get_long_long(VALUE);
}

#define PROGRAMS "programs"
#define OPCODE "opcode"
#define OPS "ops"
#define X0 "x0"
#define FITNESS "fitness"

void serialise(irept &sdu, const program_individualt &individual)
{
  irept programs;
  irept::subt &program_list=programs.get_sub();
  for (const program_individualt::programt &prog : individual.programs)
  {
    irept program;
    irept::subt &instr_list=program.get_sub();
    for (const program_individualt::instructiont &instr : prog)
    {
      irept instruction;
      instruction.set(OPCODE, instr.opcode);
      irept ops;
      irept::subt &ops_list=ops.get_sub();
      for (const program_individualt::instructiont::opt op : instr.ops)
        ops_list.push_back(singleton_irep(op));
      instruction.set(OPS, ops);
      instr_list.push_back(instruction);
    }
    program_list.push_back(program);
  }
  sdu.set(PROGRAMS, programs);
  irept x0;
  irept::subt &x0_list=x0.get_sub();
  for (const program_individualt::x0t::value_type value : individual.x0)
    x0_list.push_back(singleton_irep(value));
  sdu.set(X0, x0);
  sdu.set(FITNESS, individual.fitness);
}

void deserialise(program_individualt &individual, const irept &sdu)
{
  const irept &programs=sdu.find(PROGRAMS);
  assert(programs.is_not_nil());
  for (const irept &program : programs.get_sub())
  {
    program_individualt::programt prog;
    for (const irept &instruction : program.get_sub())
    {
      program_individualt::instructiont instr;
      instr.opcode=instruction.get_long_long(OPCODE);
      const irept &ops=instruction.find(OPS);
      assert(ops.is_not_nil());
      for (const irept &op : ops.get_sub())
        instr.ops.push_back(get_value(op));
      prog.push_back(instr);
    }
    individual.programs.push_back(prog);
  }
  const irept &x0=sdu.find(X0);
  assert(x0.is_not_nil());
  for (const irept &value : x0.get_sub())
    individual.x0.push_back(get_value(value));
  individual.fitness=sdu.get_long_long(FITNESS);
}

individual_to_danger_solution_deserialisert::individual_to_danger_solution_deserialisert(
    const danger_programt &prog, instruction_set_info_factoryt &info_fac) :
    prog(prog), info_fac(info_fac)
{
}

individual_to_danger_solution_deserialisert::~individual_to_danger_solution_deserialisert()
{
}

void individual_to_danger_solution_deserialisert::operator ()(
    danger_goto_solutiont &result, const irept &sdu) const
{
  program_individualt ind;
  deserialise(ind, sdu);
  danger_variable_idst ids;
  get_danger_variable_ids(prog.st, ids);
  const instruction_sett &instrs=info_fac.get_instructions();
  create_danger_solution(result, prog, ind, instrs, ids);
}
