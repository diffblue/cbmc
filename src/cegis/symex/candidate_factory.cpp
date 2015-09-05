/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <util/bv_arithmetic.h>

#include <goto-programs/goto_trace.h>

#include <cegis/options/literals.h>
#include <cegis/util/goto_program_adapter.h>
#include <cegis/symex/candidate_factory.h>

candidate_factoryt::candidate_factoryt(candidatet &result,
    const goto_functionst &gf, const goto_tracet &goto_trace) :
    result(result), gf(gf), goto_trace(goto_trace)
{
}

candidate_factoryt::~candidate_factoryt()
{
}

namespace {
size_t from_member(const exprt &expr)
{
  if (ID_typecast == expr.id()) return from_member(to_typecast_expr(expr).op());
  return bv_arithmetict(expr).to_integer().to_ulong();
}

const size_t OP_NUM_OFFSET_IN_SYMBOL_ID=37;
mp_integer::llong_t from_index(const exprt &expr)
{
  if (ID_typecast == expr.id()) return from_index(to_typecast_expr(expr).op());
  if (ID_symbol != expr.id()) return -1;
  const std::string &id=id2string(to_symbol_expr(expr).get_identifier());
  return string2integer(id.substr(OP_NUM_OFFSET_IN_SYMBOL_ID)).to_long();
}

const char VARS[]="__CPROVER_synthesis_vars";

bool is_operand(const exprt &expr, const size_t index)
{
  if (ID_dereference != expr.id()) return false;
  const exprt &ptr=to_dereference_expr(expr).pointer();
  if (ID_typecast != ptr.id()) return false;
  const exprt &obj=to_typecast_expr(ptr).op();
  if (ID_index != obj.id()) return false;
  const index_exprt &element=to_index_expr(obj);
  const exprt &array=element.array();
  if (ID_symbol != array.id()) return false;
  if (VARS != id2string(to_symbol_expr(array).get_identifier())) return false;
  const mp_integer::llong_t var_index=from_index(element.index());
  return var_index >= 0 && static_cast<size_t>(var_index) == index;
}

const char OPCODE_ID[]="__CPROVER_synthesis_execute::1::1::opcode";
bool is_symbol(const exprt &expr, const char * const id)
{
  const irep_idt &expr_id=expr.id();
  if (ID_typecast == expr_id) return is_symbol(to_typecast_expr(expr).op(), id);
  if (ID_symbol != expr_id) return false;
  return id2string(to_symbol_expr(expr).get_identifier()) == OPCODE_ID;
}

goto_programt::const_targett find_label(const goto_programt &prog,
    const size_t opcode)
{
  const goto_programt::instructionst &instrs=prog.instructions;
  for (goto_programt::const_targett it=instrs.begin(); it != instrs.end(); ++it)
  {
    if (GOTO != it->type) continue;
    const exprt &guard=it->guard;
    if (ID_equal != guard.id()) continue;
    const equal_exprt &comparison=to_equal_expr(guard);
    if (!is_symbol(comparison.lhs(), "opcode")) continue;
    if (opcode == from_member(comparison.rhs())) return it->get_target();
  }
  return prog.instructions.end();
}

class replace_ops_visitort: public expr_visitort
{
  const exprt &op0;
  const exprt &op1;
  const exprt &op2;
public:
  replace_ops_visitort(const exprt &op0, const exprt &op1, const exprt &op2) :
      op0(op0), op1(op1), op2(op2)
  {
  }
  ~replace_ops_visitort()
  {
  }

  virtual void operator()(exprt &expr)
  {
    exprt::operandst &ops=expr.operands();
    for (exprt::operandst::iterator it=ops.begin(); it != ops.end(); ++it)
    {
      exprt &op=*it;
      if (is_operand(op, 0)) op=op0;
      if (is_operand(op, 1)) op=op1;
      if (is_operand(op, 2)) op=op2;
    }
  }
};

goto_programt::instructiont replace_ops(
    const goto_programt::instructiont &instr, const exprt &op0,
    const exprt &op1, const exprt &op2)
{
  goto_programt::instructiont result(instr);
  replace_ops_visitort visitor(op0, op1, op2);
  result.code.visit(visitor);
  return result;
}

class instruction_convertert
{
  const goto_functionst &gf;
  const exprt::operandst &variables;
  goto_programt::instructionst &body;
public:
  instruction_convertert(const goto_functionst &gf,
      const exprt::operandst &variables, goto_programt::instructionst &body) :
      gf(gf), variables(variables), body(body)
  {
  }

  ~instruction_convertert()
  {
  }

  void operator()(const exprt &instr) const
  {
    const exprt::operandst &ops=instr.operands();
    const size_t opcode(from_member(ops.at(0)));
    const exprt &op0=variables.at(from_member(ops.at(1)));
    const exprt &op1=variables.at(from_member(ops.at(2)));
    const exprt &op2=variables.at(from_member(ops.at(3)));
    const goto_programt &exec=get_program_body(gf, SYNTHESIS_EXECUTE);
    goto_programt::const_targett current=find_label(exec, opcode);
    const goto_programt::const_targett end=exec.instructions.end();
    assert(end != current);
    goto_programt::const_targett sentinel=current;
    ++sentinel;
    const goto_programt::const_targett next=find_label(exec, opcode + 1);
    for (; end != current && end != sentinel && sentinel != next;
        ++current, ++sentinel)
      body.push_back(replace_ops(*current, op0, op1, op2));
    body.push_back(goto_programt::instructiont(END_FUNCTION));
  }
};

const char PROG_SIZE_PREFIX[]="__CPROVER_synthesis_program_size_";
bool is_size(const std::string &name)
{
  return std::string::npos != name.find(PROG_SIZE_PREFIX);
}

class handle_stept
{
  candidate_factoryt::candidatet &result;
  exprt::operandst variables;
  const goto_functionst &gf;

  bool handle_const_assignment(const std::string &name, const exprt &value)
  {
    return result.constants.insert(std::make_pair(name, value)).second;
  }

  bool handle_variables_assignment(const goto_trace_stept &step)
  {
    if (goto_trace_stept::ASSIGNMENT != step.type) return false;
    const std::string &lhs=id2string(step.lhs_object.get_identifier());
    if (std::string::npos != lhs.find(CPROVER_SYNTHESIS_TMPVAR_PREFIX))
      return handle_const_assignment(lhs, step.full_lhs_value);
    if (std::string::npos == lhs.find(VARS)) return false;
    const constant_exprt &value=to_constant_expr(step.full_lhs_value);
    const address_of_exprt &ptr=to_address_of_expr(value.op0());
    variables.push_back(ptr.object());
    return true;
  }
public:
  handle_stept(candidate_factoryt::candidatet &result,
      const goto_functionst &gf) :
      result(result), gf(gf)
  {
  }

  void operator()(const goto_trace_stept &step)
  {
    if (handle_variables_assignment(step)) return;
    if (goto_trace_stept::DECL != step.type) return;
    const std::string &lhs=id2string(step.lhs_object.get_identifier());
    if (SYNTHESIS_PROG_PREFIX_LEN >= lhs.length()) return;
    if (SYNTHESIS_PROG != lhs.substr(0, SYNTHESIS_PROG_PREFIX_LEN)) return;
    if (is_size(lhs)) return;
    const std::string function_name=lhs.substr(SYNTHESIS_PROG_PREFIX_LEN);
    candidate_factoryt::candidatet::bodiest &bodies=result.bodies;
    assert(bodies.end() == bodies.find(function_name));
    const array_exprt &value=to_array_expr(step.full_lhs_value);
    const array_exprt::operandst &instrs=value.operands();
    goto_programt::instructionst &body=bodies[function_name];
    const instruction_convertert convert_to_instr(gf, variables, body);
    std::for_each(instrs.begin(), instrs.end(), convert_to_instr);
  }
};
}

bool candidate_factoryt::operator ()() const
{
  const goto_tracet::stepst &steps=goto_trace.steps;
  const handle_stept handle_step(result, gf);
  std::for_each(steps.begin(), steps.end(), handle_step);
  return !result.bodies.empty();
}
