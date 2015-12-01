#include <util/namespace_utils.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/symex/learn/replace_operators.h>

namespace
{
const char ROP[]="__CPROVER_danger_execute::1::1::1::result";
const char OP0[]="__CPROVER_danger_execute::1::1::1::op0";
const char OP1[]="__CPROVER_danger_execute::1::1::1::op1";
const char OP2[]="__CPROVER_danger_execute::1::1::1::op2";
class replace_ops_visitort: public expr_visitort
{
private:
  const symbol_tablet &st;
  const namespacet ns;
  danger_variable_namest names;
  const danger_variable_namest &rnames;
  const size_t op0;
  const size_t op1;
  const size_t op2;
  const size_t instr_idx;
public:
  replace_ops_visitort(const symbol_tablet &st,
      const danger_variable_namest &names, const danger_variable_namest &rnames,
      const size_t op0, const size_t op1, const size_t op2,
      const size_t instr_idx) :
      st(st), ns(st), names(names), rnames(rnames), op0(op0), op1(op1), op2(
          op2), instr_idx(instr_idx)
  {
    typedef danger_variable_namest::const_iterator itt;
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
    const bool is_res=op_name == ROP;
    const bool is_op0=op_name == OP0;
    const bool is_op1=op_name == OP1;
    const bool is_op2=op_name == OP2;
    if (!is_res && !is_op0 && !is_op1 && !is_op2) return;
    const danger_variable_namest &names=is_res ? rnames : this->names;
    const size_t op=is_res ? instr_idx : is_op0 ? op0 : is_op1 ? op1 : op2;
    const danger_variable_namest::const_iterator name=names.find(op);
    assert(names.end() != name);
    const symbol_exprt symbol(st.lookup(name->second).symbol_expr());
    const typet danger_type(danger_meta_type());
    if (type_eq(danger_type, symbol.type(), ns)) expr=symbol;
    else expr=typecast_exprt(symbol, danger_type); // XXX: Change if operations for other types are added.
  }
};
}

void replace_ops_in_instr(const symbol_tablet &st,
    const goto_programt::targett &first, const goto_programt::targett &last,
    const danger_variable_namest &names, const danger_variable_namest &rnames,
    const size_t op0, const size_t op1, const size_t op2,
    const size_t instr_idx)
{
  replace_ops_visitort visitor(st, names, rnames, op0, op1, op2, instr_idx);
  for (goto_programt::targett it=first; it != last; ++it)
  {
    goto_programt::instructiont &instr=*it;
    instr.code.visit(visitor);
    instr.guard.visit(visitor);
  }
}
