#include <cegis/cegis-util/instruction_iterator.h>

#include <cegis/refactor/options/refactor_program.h>
#include <cegis/refactor/nullobject/range_collector.h>

// XXX: Debug
#include <iostream>
// XXX: Debug

namespace
{
bool is_null_comparison(const exprt &guard)
{
  const irep_idt &id=guard.id();
  if (ID_equal != id && ID_notequal != id) return false;
  const binary_relation_exprt &binary=to_binary_relation_expr(guard);
  return ID_NULL == binary.lhs().id() || ID_NULL == binary.rhs().id();
}

class null_reference_type_extractort: public const_expr_visitort
{
public:
  typet reference_type;

  virtual ~null_reference_type_extractort()=default;

  virtual void operator()(const exprt &expr)
  {
    if (ID_symbol == expr.id()) reference_type=expr.type();
  }
};

typet get_reference_type(const exprt &guard)
{
  null_reference_type_extractort extractor;
  guard.visit(extractor);
  return extractor.reference_type;
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
    if (!is_null_comparison(it->guard)) continue;
    const goto_programt::targett else_range_last(it->get_target());
    const goto_ranget else_range(++it, else_range_last);
    const goto_ranget then_range(get_then_range(else_range_last));
    if (ID_equal == it->guard.id())
    {
      prog.spec_ranges.push_back(else_range);
      prog.input_ranges.push_back(then_range);
    } else
    {
      prog.spec_ranges.push_back(then_range);
      prog.input_ranges.push_back(else_range);
    }
  }
  // XXX: Debug
  std::cout << "<collect_nullobject_range>" << std::endl;
  prog.gf.output(namespacet(prog.st), std::cout);
  std::cout << "</collect_nullobject_range>" << std::endl;
  // XXX: Debug
  // TODO: Implement
  assert(false);
}
