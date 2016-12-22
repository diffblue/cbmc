/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <goto-programs/goto_functions.h>
#include <goto-programs/remove_returns.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>

namespace
{
class symbol_visitort: public const_expr_visitort
{
  std::set<irep_idt> &vars;
public:
  explicit symbol_visitort(std::set<irep_idt> &vars) :
      vars(vars)
  {
  }

  virtual ~symbol_visitort()=default;

  virtual void operator()(const exprt &expr)
  {
    if (ID_symbol != expr.id()) return;
    vars.insert(to_symbol_expr(expr).get_identifier());
  }
};

void visit_functions(std::set<irep_idt> &vars, std::set<irep_idt> &funcs,
    const goto_functionst &gf, const goto_programt &body)
{
  symbol_visitort visitor(vars);
  for (const goto_programt::instructiont &instr : body.instructions)
  {
    instr.code.visit(visitor);
    instr.guard.visit(visitor);
    if (goto_program_instruction_typet::FUNCTION_CALL != instr.type) continue;
    const exprt &func=to_code_function_call(instr.code).function();
    assert(ID_symbol == func.id());
    const irep_idt &id=to_symbol_expr(func).get_identifier();
    funcs.insert(id);
    typedef goto_functionst::function_mapt fmapt;
    const fmapt &fmap=gf.function_map;
    const fmapt::const_iterator it=fmap.find(id);
    assert(fmap.end() != it);
    const goto_function_templatet<goto_programt> &prog=it->second;
    if (prog.body_available()) visit_functions(vars, funcs, gf, prog.body);
  }
}
}

void remove_unused_functions(symbol_tablet &st, goto_functionst &gf,
    const std::set<irep_idt> &funcs)
{
  typedef goto_functionst::function_mapt fmapt;
  fmapt &fmap=gf.function_map;
  for (fmapt::iterator it=fmap.begin(); it != fmap.end();)
  {
    const irep_idt &id=it->first;
    if (funcs.end() == funcs.find(id))
    {
      it=fmap.erase(it);
      st.remove(id);
    } else ++it;
  }
}

namespace
{
void remove_assignments_to(goto_programt &init, const irep_idt &id)
{
  goto_programt::instructionst &ins=init.instructions;
  for (goto_programt::targett pos=ins.begin(); pos != ins.end();)
  {
    const goto_programt::instructiont &instr=*pos;
    if (goto_program_instruction_typet::ASSIGN == instr.type
        && ID_symbol == to_code_assign(instr.code).lhs().id()
        && id
            == to_symbol_expr(to_code_assign(instr.code).lhs()).get_identifier())
    {
      pos=ins.erase(pos);
    } else ++pos;
  }
}

bool is_meta(const irep_idt &id)
{
  const std::string &str=id2string(id);
  return contains(str, CPROVER_PREFIX) || contains(str, RETURN_VALUE_SUFFIX);
}
}

void remove_unused_globals(symbol_tablet &st, goto_functionst &gf,
    const std::set<irep_idt> &variables)
{
  std::set<irep_idt> to_remove;
  for (const std::pair<const irep_idt, symbolt> named_symbol : st.symbols)
  {
    const symbolt &symbol=named_symbol.second;
    const irep_idt &name=named_symbol.first;
    if (symbol.is_static_lifetime && variables.end() == variables.find(name)
        && !is_meta(name)) to_remove.insert(name);
  }
  goto_programt &init=get_body(gf, CPROVER_INIT);
  for (const irep_idt &var : to_remove)
  {
    st.remove(var);
    remove_assignments_to(init, var);
  }
}

void remove_unused_elements(symbol_tablet &st, goto_functionst &gf)
{
  std::set<irep_idt> vars, funcs;
  funcs.insert(CPROVER_INIT);
  funcs.insert(goto_functionst::entry_point());
  visit_functions(vars, funcs, gf, get_entry_body(gf));
  remove_unused_functions(st, gf, funcs);
  remove_unused_globals(st, gf, vars);
}
