/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/type_eq.h>

#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/symex/learn/replace_operators.h>

namespace
{
const char ROP_SUFFIX[]="::1::1::1::result";
const char OP0_SUFFIX[]="::1::1::1::op0";
const char OP1_SUFFIX[]="::1::1::1::op1";
const char OP2_SUFFIX[]="::1::1::1::op2";
class replace_ops_visitort: public expr_visitort
{
private:
  const symbol_tablet &st;
  const namespacet ns;
  const std::string rop_name;
  const std::string op0_name;
  const std::string op1_name;
  const std::string op2_name;
  invariant_variable_namest names;
  const invariant_variable_namest &rnames;
  const size_t op0;
  const size_t op1;
  const size_t op2;
  const size_t instr_idx;
public:
  replace_ops_visitort(const symbol_tablet &st, const std::string &func_name,
      const invariant_variable_namest &names, const invariant_variable_namest &rnames,
      const size_t op0, const size_t op1, const size_t op2,
      const size_t instr_idx) :
      st(st), ns(st), rop_name(func_name + ROP_SUFFIX), op0_name(
          func_name + OP0_SUFFIX), op1_name(func_name + OP1_SUFFIX), op2_name(
          func_name + OP2_SUFFIX), names(names), rnames(rnames), op0(op0), op1(
          op1), op2(op2), instr_idx(instr_idx)
  {
    typedef invariant_variable_namest::const_iterator itt;
    const size_t offset(names.size());
    for (itt it=rnames.begin(); it != rnames.end(); ++it)
      this->names.insert(std::make_pair(offset + it->first, it->second));
  }
  virtual ~replace_ops_visitort()
  {
  }
public:
  virtual void operator()(exprt &expr)
  {
    if (ID_symbol != expr.id()) return;
    const irep_idt &op_name=to_symbol_expr(expr).get_identifier();
    const bool is_res=op_name == rop_name;
    const bool is_op0=op_name == op0_name;
    const bool is_op1=op_name == op1_name;
    const bool is_op2=op_name == op2_name;
    if (!is_res && !is_op0 && !is_op1 && !is_op2) return;
    const invariant_variable_namest &names=is_res ? rnames : this->names;
    const size_t op=is_res ? instr_idx : is_op0 ? op0 : is_op1 ? op1 : op2;
    const invariant_variable_namest::const_iterator name=names.find(op);
    assert(names.end() != name);
    const symbol_exprt symbol(st.lookup(name->second).symbol_expr());
    const typet danger_type(cegis_default_integer_type());
    if (type_eq(danger_type, symbol.type(), ns)) expr=symbol;
    else expr=typecast_exprt(symbol, danger_type); // XXX: Change if operations for other types are added.
  }
};
}

void replace_ops_in_instr(const symbol_tablet &st, const std::string &func,
    const goto_programt::targett &first, const goto_programt::targett &last,
    const invariant_variable_namest &names, const invariant_variable_namest &rnames,
    const size_t op0, const size_t op1, const size_t op2,
    const size_t instr_idx)
{
  replace_ops_visitort v(st, func, names, rnames, op0, op1, op2, instr_idx);
  for (goto_programt::targett it=first; it != last; ++it)
  {
    goto_programt::instructiont &instr=*it;
    instr.code.visit(v);
    instr.guard.visit(v);
  }
}

void reverse_invariant_var_ids(invariant_variable_namest &names,
    const operand_variable_idst &ids)
{
  for (const auto id : ids)
    names.insert(std::make_pair(id.second, id.first));
}
