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

bool is_null_comparison(const exprt &guard)
{
  const irep_idt &id=guard.id();
  if (ID_equal != id && ID_notequal != id) return false;
  const binary_relation_exprt &binary=to_binary_relation_expr(guard);
  return is_null(binary.lhs()) || is_null(binary.rhs());
}

goto_ranget get_then_range(const goto_programt::targett &else_range_last)
{
  const goto_programt::targett then_range_first(else_range_last);
  const goto_programt::targett last_else_instr(std::prev(else_range_last));
  if (GOTO != last_else_instr->type)
    return goto_ranget(then_range_first, then_range_first);
  return goto_ranget(then_range_first, last_else_instr->get_target());
}
}

void collect_nullobject_ranges(refactor_programt &prog)
{
  for (instr_iteratort it(prog.gf); it != instr_iteratort::end; ++it)
  {
    if (goto_program_instruction_typet::GOTO != it->type) continue;
    const exprt &guard=it->guard;
    if (!is_null_comparison(guard)) continue;
    prog.sketches.push_back(refactor_programt::sketcht());
    refactor_programt::sketcht &sketch=prog.sketches.back();
    sketch.init=it;
    const goto_programt::targett else_range_last(it->get_target());
    const goto_ranget else_range(++it, else_range_last);
    const goto_ranget then_range(get_then_range(else_range_last));
    if (ID_equal == guard.id())
    {
      sketch.spec_range=then_range;
      sketch.input_range=else_range;
    } else
    {
      sketch.spec_range=else_range;
      sketch.input_range=then_range;
    }
    sketch.types=collect_context_types(then_range);
    const std::set<typet> tmp(collect_context_types(else_range));
    sketch.types.insert(tmp.begin(), tmp.end());
  }
}
