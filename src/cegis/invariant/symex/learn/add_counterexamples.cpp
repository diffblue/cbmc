/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <ansi-c/c_types.h>

#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/symex/learn/add_counterexamples.h>

namespace
{
typedef std::map<const irep_idt, array_exprt> array_valuest;

typedef counterexamplet::const_iterator ceitt;
class create_x_array_valuest
{
  array_valuest &vals;
  const counterexamplet &prototype;
  const size_t num_ces;
public:
  array_valuest::value_type to_array(const ceitt &it, const exprt &size)
  {
    const array_exprt array(array_typet(it->second.type(), size));
    return std::make_pair(it->first, array);
  }

  create_x_array_valuest(array_valuest &vals, const counterexamplet &prototype,
      const size_t num_ces) :
      vals(vals), prototype(prototype), num_ces(num_ces)
  {
    const constant_exprt size(from_integer(num_ces, unsigned_int_type()));
    for (ceitt it=prototype.begin(); it != prototype.end(); ++it)
      vals.insert(to_array(it, size));
  }

  void operator()(const counterexamplet &ce) const
  {
    for (ceitt it=ce.begin(); it != ce.end(); ++it)
      vals[it->first].copy_to_operands(it->second);
  }
};

void declare_x_arrays(symbol_tablet &st, goto_functionst &gf,
    goto_programt::targett pos, const array_valuest &vals,
    const std::string &meta_var_prefix)
{
  for (array_valuest::const_iterator it=vals.begin(); it != vals.end(); ++it)
  {
    std::string base_name(meta_var_prefix);
    base_name+=id2string(it->first);
    const array_exprt &value=it->second;
    const typet &type=value.type();
    pos=declare_cegis_meta_variable(st, gf, pos, base_name, type);
    pos=assign_cegis_meta_variable(st, gf, pos, base_name, value);
  }
}

const char X_INDEX[]=CEGIS_PREFIX "x_index";
symbol_exprt get_index(const symbol_tablet &st)
{
  const std::string index_name(get_cegis_meta_name(X_INDEX));
  return st.lookup(index_name).symbol_expr();
}

goto_programt::targett find_decl(goto_programt::targett begin,
    const goto_programt::targett &end, const irep_idt &id)
{
  for (; begin != end; ++begin)
    if (begin->is_decl() && get_affected_variable(*begin) == id) return begin;
  return end;
}

class assign_ce_valuet
{
  const invariant_programt &prog;
  const symbol_tablet &st;
  goto_functionst &gf;
  goto_programt::targett pos;
  goto_programt::targett goto_pos;
  const std::string meta_var_prefix;
  const bool use_x0_ce;
public:
  void add_x0_case(const size_t ces_size)
  {
    const typet size_type(unsigned_int_type());
    const constant_exprt num_ces(from_integer(ces_size, size_type));
    const symbol_exprt index(get_index(st));
    const equal_exprt cond(index, num_ces);
    pos->guard=cond;
    goto_pos=pos;
  }

  assign_ce_valuet(invariant_programt &prog, const size_t ces_size,
      const goto_programt::targett begin_pos,
      const std::string &meta_var_prefix, const bool use_x0_ce) :
      prog(prog), st(prog.st), gf(prog.gf), meta_var_prefix(meta_var_prefix), use_x0_ce(
          use_x0_ce)
  {
    const invariant_programt::invariant_loopst loops(prog.get_loops());
    assert(!loops.empty());
    pos=begin_pos;
    ++pos;
    if (use_x0_ce)
    {
      pos=get_entry_body(gf).insert_after(pos);
      pos->type=goto_program_instruction_typet::GOTO;
      pos->source_location=default_cegis_source_location();
      add_x0_case(ces_size);
    }
  }

  void operator()(const std::pair<const irep_idt, exprt> &assignment)
  {
    std::string base_name(meta_var_prefix);
    base_name+=id2string(assignment.first);
    const std::string array_name(get_cegis_meta_name(base_name));
    const symbol_exprt array(st.lookup(array_name).symbol_expr());
    const index_exprt rhs(array, get_index(st));
    const irep_idt &id=assignment.first;
    const symbol_exprt lhs(st.lookup(id).symbol_expr());
    const goto_programt::targett end(prog.invariant_range.end);
    const goto_programt::targett decl(find_decl(pos, end, id));
    if (end == decl) pos=cegis_assign(st, gf, pos, lhs, rhs);
    else cegis_assign(st, gf, decl, lhs, rhs);
  }

  void finalize_x0_case()
  {
    if (use_x0_ce) goto_pos->targets.push_back(++pos);
  }
};

void create_constraints(invariant_programt &prog,
    const constraint_factoryt &constraint)
{
  goto_programt::targett pos=prog.invariant_range.end;
  std::advance(pos, -3);
  goto_programt &body=get_entry_body(prog.gf);
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSUME;
  pos->source_location=default_cegis_source_location();
  pos->guard=constraint(prog.get_loops().size());
}

void add_final_assertion(invariant_programt &prog,
    const goto_programt::targett &loop_end)
{
  goto_programt &body=get_entry_body(prog.gf);
  goto_programt::targett assertion=body.insert_after(loop_end);
  assertion->type=goto_program_instruction_typet::ASSERT;
  assertion->source_location=default_cegis_source_location();
  assertion->guard=false_exprt();
}
}

void invariant_declare_x_choice_arrays(invariant_programt &prog,
    const counterexamplest &ces, const std::string &meta_var_prefix)
{
  array_valuest vals;
  const create_x_array_valuest create_values(vals, ces.front(), ces.size());
  std::for_each(ces.begin(), ces.end(), create_values);
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt::targett pos=prog.invariant_range.begin;
  declare_x_arrays(st, gf, --pos, vals, meta_var_prefix);
}

namespace
{
const char X_LABEL[]=CEGIS_PREFIX"x_loop";
}

goto_programt::targett invariant_add_ce_loop(invariant_programt &prog,
    const size_t ces_size, const bool use_x0_ce)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt::targett pos=prog.invariant_range.begin;
  const typet size_type(unsigned_int_type());
  pos=declare_cegis_meta_variable(st, gf, --pos, X_INDEX, size_type);
  const constant_exprt first_index(from_integer(0, size_type));
  pos=assign_cegis_meta_variable(st, gf, pos, X_INDEX, first_index);
  goto_programt::targett loop_head=pos;
  (++loop_head)->labels.push_back(X_LABEL);
  goto_programt &body=get_entry_body(gf);
  pos=insert_before_preserve_labels(body, prog.invariant_range.end);
  pos->type=goto_program_instruction_typet::ASSIGN;
  pos->source_location=default_cegis_source_location();
  const symbol_exprt index(get_index(st));
  const constant_exprt one(from_integer(1, size_type));
  const code_assignt inc(index, plus_exprt(index, one));
  pos->code=inc;
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::GOTO;
  pos->source_location=default_cegis_source_location();
  pos->function=goto_functionst::entry_point();
  pos->targets.push_back(loop_head);
  pos->loop_number=0u;
  const size_t loop_limit=use_x0_ce ? ces_size + 1 : ces_size;
  const constant_exprt num_ces(from_integer(loop_limit, size_type));
  const binary_relation_exprt cond(index, ID_lt, num_ces);
  pos->guard=cond;
  return pos;
}

void invariant_assign_ce_values(invariant_programt &prog,
    const counterexamplet &prototype_ce, const size_t num_ces,
    const std::string &prefix, const goto_programt::targett pos,
    const bool use_x0_ce)
{
  const assign_ce_valuet assign_value(prog, num_ces, pos, prefix, use_x0_ce);
  std::for_each(prototype_ce.begin(), prototype_ce.end(), assign_value).finalize_x0_case();
}

void invariant_add_constraint(invariant_programt &prog,
    const constraint_factoryt constraint,
    const goto_programt::targett &ce_loop_end)
{
  create_constraints(prog, constraint);
  add_final_assertion(prog, ce_loop_end);
}

void invariant_add_learned_counterexamples(invariant_programt &prog,
    const counterexamplest &ces, const constraint_factoryt constraint,
    const bool x0_ce)
{
  // TODO: Danger counterexamples need one map<irep_idt, exprt> per loop (per quantifier)!
  if (ces.empty()) return;
  const std::string pre(X_CHOICE_PREFIX);
  invariant_declare_x_choice_arrays(prog, ces, pre);
  const size_t sz=ces.size();
  const goto_programt::targett loop_end=invariant_add_ce_loop(prog, sz, x0_ce);
  const goto_programt::targett pos=prog.get_loops().front()->meta_variables.Ix;
  invariant_assign_ce_values(prog, ces.front(), ces.size(), pre, pos, x0_ce);
  invariant_add_constraint(prog, constraint, loop_end);
}
