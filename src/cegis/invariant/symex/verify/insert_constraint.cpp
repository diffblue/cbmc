/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/cprover_prefix.h>
#include <util/expr_util.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/util/invariant_constraint_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/symex/verify/insert_constraint.h>

namespace
{
class quantifyt
{
  goto_programt::targetst &quantifiers;
  goto_programt::targett pos;
  goto_programt &body;
  size_t quantifier_count;
public:
  quantifyt(goto_programt::targetst &quantifiers,
      const goto_programt::targett &pos, invariant_programt &program,
      const size_t quantifier_label_offset) :
      quantifiers(quantifiers), pos(pos), body(get_entry_body(program.gf)), quantifier_count(
          quantifier_label_offset)
  {
  }

  void operator()(const symbol_exprt &var)
  {
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::ASSIGN;
    pos->source_location=default_cegis_source_location();
    pos->code=code_assignt(var, side_effect_expr_nondett(var.type()));
    std::string label(DANGER_CE_QUANTIFIER_LABEL_PREFIX);
    label+=integer2string(quantifier_count++);
    pos->labels.push_back(label);
    quantifiers.push_back(pos);
  }
};

void add_universal_quantifier(goto_programt::targetst &quantifiers,
    invariant_programt &program, const size_t quantifier_label_offset)
{
  invariant_symbol_set vars(create_empty_symbol_set());
  collect_counterexample_variables(vars, program);
  goto_programt::targett Ix=program.get_loops().front()->meta_variables.Ix;
  const quantifyt quantify(quantifiers, --Ix, program, quantifier_label_offset);
  std::for_each(vars.begin(), vars.end(), quantify);
}

void add_final_assertion(invariant_programt &program,
    const constraint_factoryt &constraint_factory)
{
  goto_programt::targett pos=program.invariant_range.end;
  pos=get_entry_body(program.gf).insert_after(--pos);
  pos->type=goto_program_instruction_typet::ASSERT;
  pos->source_location=default_cegis_source_location();
  pos->guard=constraint_factory(program.get_loops().size());
}
}

void invariant_insert_constraint(goto_programt::targetst &quantifiers,
    invariant_programt &program, const constraint_factoryt constraint_factory,
    const size_t quantifier_label_offset)
{
  add_universal_quantifier(quantifiers, program, quantifier_label_offset);
  add_final_assertion(program, constraint_factory);
}
