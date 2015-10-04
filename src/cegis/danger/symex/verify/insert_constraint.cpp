#include <algorithm>

#include <util/cprover_prefix.h>

#include <cegis/danger/constraint/danger_constraint_factory.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/symex/verify/insert_constraint.h>

namespace
{
bool is_meta(const irep_idt &id, const typet &type)
{
  if (ID_code == type.id()) return true;
  const std::string &name=id2string(id);
  if (std::string::npos != name.find("#return_value")) return true;
  return std::string::npos != name.find(CPROVER_PREFIX);
}

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
  if (is_local(id2string(symbol.name))) return true;
  return is_const(symbol.type);
}

typedef bool (*symbol_comparatort)(const symbol_exprt &, const symbol_exprt &);

typedef std::set<symbol_exprt, symbol_comparatort> danger_symbol_set;

class counterexample_variable_collectort
{
  danger_symbol_set &vars;
public:
  counterexample_variable_collectort(danger_symbol_set &vars) :
      vars(vars)
  {
  }

  void operator()(const goto_programt::instructiont &instr) const
  {
    if (goto_program_instruction_typet::DECL != instr.type) return;
    const code_declt &code_decl=to_code_decl(instr.code);
    const symbol_exprt &symbol=to_symbol_expr(code_decl.symbol());
    const typet &type=symbol.type();
    if (is_const(type)) return;
    if (is_meta(symbol.get_identifier(), type)) return;
    vars.insert(symbol);
  }

  void operator()(const std::pair<const irep_idt, symbolt> &named_symbol) const
  {
    const symbolt &symbol=named_symbol.second;
    if (is_local_or_constant(symbol) || is_meta(symbol.name, symbol.type))
      return;
    vars.insert(symbol.symbol_expr());
  }
};

void collect_counterexample_variables(danger_symbol_set &vars,
    const danger_programt &program)
{
  const counterexample_variable_collectort collector(vars);
  const symbol_tablet &st=program.st;
  std::for_each(st.symbols.begin(), st.symbols.end(), collector);
  const goto_programt::targett Dx=program.loops.front().meta_variables.Dx;
  std::for_each(program.danger_range.begin, Dx, collector);
}

class quantifyt
{
  goto_programt::targetst &quantifiers;
  goto_programt::targett pos;
  goto_programt &body;
public:
  quantifyt(goto_programt::targetst &quantifiers,
      const goto_programt::targett &pos, danger_programt &program) :
      quantifiers(quantifiers), pos(pos), body(get_danger_body(program.gf))
  {
  }

  void operator()(const symbol_exprt &var)
  {
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::ASSIGN;
    pos->source_location=default_danger_source_location();
    pos->code=code_assignt(var, side_effect_expr_nondett(var.type()));
    quantifiers.push_back(pos);
  }
};

bool compare_symbol(const symbol_exprt &lhs, const symbol_exprt &rhs)
{
  return lhs.get_identifier() < rhs.get_identifier();
}

void add_universal_quantifier(goto_programt::targetst &quantifiers,
    danger_programt &program)
{
  danger_symbol_set vars(&compare_symbol);
  collect_counterexample_variables(vars, program);
  goto_programt::targett Dx=program.loops.front().meta_variables.Dx;
  const quantifyt quantify(quantifiers, --Dx, program);
  std::for_each(vars.begin(), vars.end(), quantify);
}

void add_final_assertion(danger_programt &program)
{
  goto_programt::targett pos=program.danger_range.end;
  pos=get_danger_body(program.gf).insert_after(--pos);
  pos->type=goto_program_instruction_typet::ASSERT;
  pos->source_location=default_danger_source_location();
  pos->guard=create_danger_constraint(program.loops.size());
}
}

void danger_insert_constraint(goto_programt::targetst &quantifiers,
    danger_programt &program)
{
  add_universal_quantifier(quantifiers, program);
  add_final_assertion(program);
}

void get_danger_constraint_vars(constraint_varst &vars,
    const danger_programt &program)
{
  danger_symbol_set smb(&compare_symbol);
  collect_counterexample_variables(smb, program);
  std::copy(smb.begin(), smb.end(), std::back_inserter(vars));
}
