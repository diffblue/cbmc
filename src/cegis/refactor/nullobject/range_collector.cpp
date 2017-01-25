/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/instruction_iterator.h>
#include <cegis/refactor/options/refactor_program.h>
#include <cegis/refactor/instructionset/create_cegis_processor.h>
#include <cegis/refactor/nullobject/range_collector.h>

namespace
{
bool is_null(const exprt &expr)
{
  if (ID_constant != expr.id()) return false;
  return ID_NULL == to_constant_expr(expr).get_value();
}

class is_null_comparisont
{
public:
  pointer_typet nulled_type;
private:
  bool extract_nulled_type(const exprt &operand)
  {
    if (ID_typecast == operand.id())
      return extract_nulled_type(to_typecast_expr(operand).op());
    nulled_type=to_pointer_type(to_symbol_expr(operand).type());
    return true;
  }
public:
  bool operator()(const exprt &guard)
  {
    const irep_idt &id=guard.id();
    if (ID_equal != id && ID_notequal != id) return false;
    const binary_relation_exprt &binary=to_binary_relation_expr(guard);
    const exprt &lhs=binary.lhs();
    const exprt &rhs=binary.rhs();
    if (is_null(lhs)) return extract_nulled_type(rhs);
    else if (is_null(rhs)) return extract_nulled_type(lhs);
    return false;
  }
};

goto_ranget get_then_range(const goto_programt::targett &else_range_last)
{
  const goto_programt::targett then_range_first(else_range_last);
  const goto_programt::targett last_else_instr(std::prev(else_range_last));
  if (GOTO != last_else_instr->type)
    return goto_ranget(then_range_first, then_range_first);
  return goto_ranget(then_range_first, last_else_instr->get_target());
}

goto_programt::targett get_else_range_last(const goto_programt::targett pos)
{
  const goto_programt::targett prev=std::prev(pos);
  if (goto_program_instruction_typet::GOTO != prev->type
      || prev->is_backwards_goto()) return pos;
  return prev;
}
}

void collect_nullobject_ranges(refactor_programt &prog)
{
  for (instr_iteratort it(prog.gf); it != instr_iteratort::end; ++it)
  {
    if (goto_program_instruction_typet::GOTO != it->type) continue;
    const exprt &guard=it->guard;
    is_null_comparisont is_null_comparison;
    if (!is_null_comparison(guard)) continue;
    prog.sketches.push_back(refactor_programt::sketcht());
    refactor_programt::sketcht &sketch=prog.sketches.back();
    sketch.init=it;
    const goto_programt::targett then_target=it->get_target();
    const goto_programt::targett else_last=get_else_range_last(then_target);
    const goto_ranget else_range(++it, else_last);
    const goto_ranget then_range(get_then_range(then_target));
    if (ID_equal == guard.id())
    {
      sketch.spec_range=then_range;
      sketch.input_range=else_range;
    } else
    {
      sketch.spec_range=else_range;
      sketch.input_range=then_range;
    }
    refactor_programt::sketcht::typest &types=sketch.types;
    types=collect_context_types(then_range);
    const auto tmp(collect_context_types(else_range));
    types.insert(tmp.begin(), tmp.end());
    pointer_typet &nulled_type=is_null_comparison.nulled_type;
    types.erase(nulled_type);
    nulled_type.set(CEGIS_NULLED_TYPE_ID, true);
    types.insert(nulled_type);
  }
}
