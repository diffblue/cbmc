/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <util/cprover_prefix.h>

#include <goto-programs/goto_program.h>

#include <cegis/instrument/literals.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/util/invariant_constraint_variables.h>

namespace
{
bool is_local(const std::string &name)
{
  return std::string::npos != name.find("::"); // XXX: Better way to do this?
}

bool is_const(const typet &type)
{
  return type.get_bool(ID_C_constant);
}

bool is_local_or_constant(const symbolt &symbol)
{
  if(is_local(id2string(symbol.name))) return true;
  return is_const(symbol.type);
}

bool is_meta(const irep_idt &id, const typet &type)
{
  if(ID_code == type.id()) return true;
  const std::string &name=id2string(id);
  if(std::string::npos != name.find(CEGIS_CONSTANT_PREFIX)) return true;
  if(std::string::npos != name.find("#return_value")) return true;
  return std::string::npos != name.find(CPROVER_PREFIX);
}

class counterexample_variable_collectort
{
  invariant_symbol_set &vars;
public:
  explicit counterexample_variable_collectort(invariant_symbol_set &vars) :
      vars(vars)
  {
  }

  void operator()(const goto_programt::instructiont &instr) const
  {
    if(goto_program_instruction_typet::DECL != instr.type) return;
    const code_declt &code_decl=to_code_decl(instr.code);
    const symbol_exprt &symbol=to_symbol_expr(code_decl.symbol());
    const typet &type=symbol.type();
    if(is_const(type)) return;
    if(is_meta(symbol.get_identifier(), type)) return;
    vars.insert(symbol);
  }

  void operator()(const std::pair<const irep_idt, symbolt> &named_symbol) const
  {
    const symbolt &symbol=named_symbol.second;
    if(is_local_or_constant(symbol) || is_meta(symbol.name, symbol.type))
      return;
    vars.insert(symbol.symbol_expr());
  }
};

bool compare_symbol_by_id(const symbol_exprt &lhs, const symbol_exprt &rhs)
{
  return lhs.get_identifier() < rhs.get_identifier();
}
}

void collect_counterexample_variables(invariant_symbol_set &vars,
    const invariant_programt &program)
{
  const counterexample_variable_collectort collector(vars);
  const symbol_tablet &st=program.st;
  std::for_each(st.symbols.begin(), st.symbols.end(), collector);
  const invariant_programt::const_invariant_loopst loops(program.get_loops());
  assert(!loops.empty());
  const goto_programt::targett Ix=loops.front()->meta_variables.Ix;
  std::for_each(program.invariant_range.begin, Ix, collector);
}

void get_invariant_constraint_vars(constraint_varst &vars,
    const invariant_programt &program)
{
  invariant_symbol_set smb(&compare_symbol_by_id);
  collect_counterexample_variables(smb, program);
  std::copy(smb.begin(), smb.end(), std::back_inserter(vars));
}

invariant_symbol_set create_empty_symbol_set()
{
  return invariant_symbol_set(&compare_symbol_by_id);
}
