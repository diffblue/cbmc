/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

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

void refactor_symex_verifyt::process(const candidatet &candidate)
{
  current_program=original_program;
  symbol_tablet &st=current_program.st;
  goto_functionst &gf=current_program.gf;
  const namespacet ns(st);
  for(const irep_idt &program : current_program.programs)
  {
    symbolt &symbol=st.lookup(program);
    const candidatet::const_iterator it=candidate.find(program);
    if(candidate.end() == it)
    {
      const exprt zero(zero_initializer(symbol.type, symbol.location, ns));
      assign_in_cprover_init(gf, symbol, zero);
    } else assign_in_cprover_init(gf, symbol, it->second);
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
