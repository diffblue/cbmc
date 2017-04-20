/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>

#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/clone_heap.h>
#include <cegis/jsa/converters/replace_operators.h>

#define INSTR "instr"
#define OPCODE "opcode"
#define ROP "result_op"
#define OP0 "op0"
#define OP1 "op1"
#define LOCAL_HEAP "heap"
#define LOCAL_LIST "list"
#define LOCAL_IT "it"

namespace
{
bool is_instr_name(const std::string &name)
{
  return std::string::npos != name.find(JSA_PRED_EXEC)
      && std::string::npos != name.find(INSTR);
}

class replace_pred_ops_visitort: public expr_visitort
{
  const __CPROVER_jsa_pred_instructiont &instr;
public:
  explicit replace_pred_ops_visitort(
    const __CPROVER_jsa_pred_instructiont &instr):instr(instr)
  {
  }

  virtual void operator()(exprt &expr)
  {
    if(ID_typecast != expr.id()) return;
    const typecast_exprt &cast=to_typecast_expr(expr);
    const exprt &cast_op=cast.op();
    if(ID_member != cast_op.id()) return;
    const member_exprt &member=to_member_expr(cast_op);
    const exprt &compound=member.compound();
    if(ID_symbol != compound.id()) return;
    const irep_idt &compound_id=to_symbol_expr(compound).get_identifier();
    if(!is_instr_name(id2string(compound_id))) return;
    const std::string &component=id2string(member.get_component_name());
    const typet &type=cast.type();
    if(ROP == component) expr=from_integer(instr.result_op, type);
    else if(OP0 == component) expr=from_integer(instr.op0, type);
    else if(OP1 == component) expr=from_integer(instr.op1, type);
    else assert(!"Illegal compound member");
  }
};
}

void replace_pred_ops(goto_programt::targett first,
    const goto_programt::const_targett &last,
    const __CPROVER_jsa_pred_instructiont &instr)
{
  replace_pred_ops_visitort visitor(instr);
  for(; first != last; ++first)
  {
    first->guard.visit(visitor);
    first->code.visit(visitor);
  }
}

namespace
{
class replace_query_ops_visitort: public expr_visitort
{
  const symbol_tablet &st;
  const __CPROVER_jsa_query_instructiont &instr;
  const __CPROVER_jsa_query_instructiont &prefix;
  std::vector<exprt *> heap_occurrences;
public:
  replace_query_ops_visitort(const symbol_tablet &st,
      const __CPROVER_jsa_query_instructiont &instr,
      const __CPROVER_jsa_query_instructiont &prefix) :
      st(st), instr(instr), prefix(prefix)
  {
  }

  ~replace_query_ops_visitort()
  {
    for(exprt * const expr : heap_occurrences)
      *expr=address_of_exprt(get_queried_heap(st));
  }

  void handle_member(member_exprt &member_expr)
  {
    const exprt &compound=member_expr.compound();
    if(ID_symbol != compound.id()) return;
    const std::string &id=id2string(to_symbol_expr(compound).get_identifier());
    if(std::string::npos == id.find(INSTR)) return;
    const std::string &member=id2string(member_expr.get_component_name());
    exprt &expr=static_cast<exprt &>(member_expr);
    if(OP0 == member) expr=from_integer(instr.op0, expr.type());
    else if(OP1 == member) expr=from_integer(instr.op1, expr.type());
    else if(OPCODE == member) expr=from_integer(instr.opcode, expr.type());
    else assert(!"Illegal compound member");
  }

  virtual void operator()(exprt &expr)
  {
    const irep_idt &expr_id=expr.id();
    if(ID_member == expr_id) return handle_member(to_member_expr(expr));
    if(ID_symbol != expr_id) return;
    const std::string &id=id2string(to_symbol_expr(expr).get_identifier());
    if(std::string::npos != id.find(LOCAL_HEAP)) heap_occurrences.push_back(
        &expr);
    else if(std::string::npos != id.find(LOCAL_LIST)) expr=from_integer(
        prefix.opcode, expr.type());
    else if(std::string::npos != id.find(LOCAL_IT))
      expr=from_integer(prefix.op0, expr.type());
  }
};
}

void replace_query_ops(const symbol_tablet &st, goto_programt::targett first,
    const goto_programt::const_targett &last,
    const __CPROVER_jsa_query_instructiont &instr,
    const __CPROVER_jsa_query_instructiont &prefix)
{
  replace_query_ops_visitort visitor(st, instr, prefix);
  for(; first != last; ++first)
  {
    first->guard.visit(visitor);
    first->code.visit(visitor);
  }
}
