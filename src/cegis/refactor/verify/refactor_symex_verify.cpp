#include <algorithm>
#include <functional>

#include <linking/zero_initializer.h>

#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/refactor/verify/refactor_symex_verify.h>

refactor_symex_verifyt::refactor_symex_verifyt(const refactor_programt &prog) :
    original_program(prog)
{
}

namespace
{
void init_value(goto_functionst &gf, symbolt &symbol, const exprt &value)
{
  symbol.value=value;
  goto_programt &body=get_body(gf, CPROVER_INIT);
  goto_programt::instructionst &instrs=body.instructions;
  const auto op(std::mem_fun_ref(&goto_programt::instructiont::is_end_function));
  goto_programt::targett pos=std::find_if(instrs.begin(), instrs.end(), op);
  assert(instrs.end() != pos);
  pos=insert_before_preserving_source_location(body, pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  const symbol_exprt lhs(symbol.symbol_expr());
  pos->code=code_assignt(lhs, value);
}
}

void refactor_symex_verifyt::process(const candidatet &candidate)
{
  current_program=original_program;
  symbol_tablet &st=current_program.st;
  goto_functionst &gf=current_program.gf;
  const namespacet ns(st);
  null_message_handlert msg;
  for (const irep_idt &program : current_program.programs)
  {
    symbolt &symbol=st.lookup(program);
    const candidatet::const_iterator it=candidate.find(program);
    if (candidate.end() == it)
    {
      const exprt zero(zero_initializer(symbol.type, symbol.location, ns, msg));
      init_value(gf, symbol, zero);
    } else init_value(gf, symbol, it->second);
  }
}

const symbol_tablet &refactor_symex_verifyt::get_symbol_table() const
{
  return current_program.st;
}

const goto_functionst &refactor_symex_verifyt::get_goto_functions() const
{
  return current_program.gf;
}

void refactor_symex_verifyt::convert(counterexamplest &counterexamples,
    const goto_tracet &trace) const
{
  counterexamples.push_back(extract_counterexample(trace));
}

void refactor_symex_verifyt::show_counterexample(messaget::mstreamt &os,
    const counterexamplet &counterexample) const
{
  show_assignments(os, counterexample);
}
