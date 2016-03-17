#include <algorithm>

#include <util/cprover_prefix.h>
#include <util/expr_util.h>

#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/util/invariant_constraint_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/instrument/meta_variables.h>
#include <cegis/invariant/symex/verify/insert_constraint.h>

namespace
{
class quantifyt
{
  goto_programt::targetst &quantifiers;
  goto_programt::targett pos;
  goto_programt &body;
public:
  quantifyt(goto_programt::targetst &quantifiers,
      const goto_programt::targett &pos, invariant_programt &program) :
      quantifiers(quantifiers), pos(pos), body(get_entry_body(program.gf))
  {
  }

  void operator()(const symbol_exprt &var)
  {
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::ASSIGN;
    pos->source_location=default_invariant_source_location();
    pos->code=code_assignt(var, side_effect_expr_nondett(var.type()));
    quantifiers.push_back(pos);
  }
};

void add_universal_quantifier(goto_programt::targetst &quantifiers,
    invariant_programt &program)
{
  invariant_symbol_set vars(create_empty_symbol_set());
  collect_counterexample_variables(vars, program);
  goto_programt::targett Ix=program.get_loops().front()->meta_variables.Ix;
  const quantifyt quantify(quantifiers, --Ix, program);
  std::for_each(vars.begin(), vars.end(), quantify);
}

void add_final_assertion(invariant_programt &program,
    const constraint_factoryt &constraint_factory)
{
  goto_programt::targett pos=program.invariant_range.end;
  pos=get_entry_body(program.gf).insert_after(--pos);
  pos->type=goto_program_instruction_typet::ASSERT;
  pos->source_location=default_invariant_source_location();
  pos->guard=constraint_factory(program.get_loops().size());
}
}

void invariant_insert_constraint(goto_programt::targetst &quantifiers,
    invariant_programt &program, const constraint_factoryt constraint_factory)
{
  add_universal_quantifier(quantifiers, program);
  add_final_assertion(program, constraint_factory);
}
