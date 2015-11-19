#include <algorithm>

#include <ansi-c/c_types.h>

#include <util/arith_tools.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/constraint/danger_constraint_factory.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/symex/learn/add_counterexamples.h>

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

const char X_CHOICE_PREFIX[]=DANGER_PREFIX"x_choice_";
void declare_x_arrays(symbol_tablet &st, goto_functionst &gf,
    goto_programt::targett pos, const array_valuest &vals)
{
  for (array_valuest::const_iterator it=vals.begin(); it != vals.end(); ++it)
  {
    std::string base_name(X_CHOICE_PREFIX);
    base_name+=id2string(it->first);
    const array_exprt &value=it->second;
    const typet &type=value.type();
    pos=declare_danger_variable(st, gf, pos, base_name, type);
    pos=assign_danger_variable(st, gf, pos, base_name, value);
  }
}

const char X_LABEL[]=DANGER_PREFIX"x_loop";
const char X_INDEX[]=DANGER_PREFIX"x_index";
goto_programt::targett add_ce_loop(danger_programt &prog, const size_t ces_size)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt::targett pos=prog.danger_range.begin;
  const typet size_type(unsigned_int_type());
  pos=declare_danger_variable(st, gf, --pos, X_INDEX, size_type);
  const constant_exprt first_index(from_integer(0, size_type));
  pos=assign_danger_variable(st, gf, pos, X_INDEX, first_index);
  goto_programt::targett loop_head=pos;
  (++loop_head)->labels.push_back(X_LABEL);
  goto_programt &body=get_danger_body(gf);
  pos=body.insert_before(prog.danger_range.end);
  pos->type=goto_program_instruction_typet::ASSIGN;
  pos->source_location=default_danger_source_location();
  const std::string index_name(get_danger_meta_name(X_INDEX));
  const symbol_exprt index(st.lookup(index_name).symbol_expr());
  const constant_exprt one(from_integer(1, size_type));
  const code_assignt inc(index, plus_exprt(index, one));
  pos->code=inc;
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::GOTO;
  pos->source_location=default_danger_source_location();
  pos->targets.push_back(loop_head);
  pos->loop_number=0u;
  const constant_exprt num_ces(from_integer(ces_size, size_type));
  const binary_relation_exprt cond(index, ID_lt, num_ces);
  pos->guard=cond;
  return pos;
}

class assign_ce_valuet
{
  const symbol_tablet &st;
  goto_functionst &gf;
  goto_programt::targett pos;
public:
  assign_ce_valuet(danger_programt &prog) :
      st(prog.st), gf(prog.gf)
  {
    const danger_programt::loopst &loops=prog.loops;
    assert(!loops.empty());
    pos=loops.begin()->meta_variables.Dx;
    ++pos;
  }

  void operator()(const std::pair<const irep_idt, exprt> &assignment)
  {
    std::string base_name(X_CHOICE_PREFIX);
    base_name+=id2string(assignment.first);
    const std::string array_name(get_danger_meta_name(base_name));
    const symbol_exprt array(st.lookup(array_name).symbol_expr());
    const std::string index_name(get_danger_meta_name(X_INDEX));
    const symbol_exprt index(st.lookup(index_name).symbol_expr());
    const index_exprt rhs(array, index);
    const symbol_exprt lhs(st.lookup(assignment.first).symbol_expr());
    pos=danger_assign(st, gf, pos, lhs, rhs);
  }
};

void assign_ce_values(danger_programt &prog, const counterexamplet &ce)
{
  const assign_ce_valuet assign_value(prog);
  std::for_each(ce.begin(), ce.end(), assign_value);
}

//const char CONSTRAINTS[]=DANGER_PREFIX "constraints";

void create_constraints(danger_programt &prog)
{
  goto_programt::targett pos=prog.danger_range.end;
  std::advance(pos, -3);
  goto_programt &body=get_danger_body(prog.gf);
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSUME;
  pos->source_location=default_danger_source_location();
  pos->guard=create_danger_constraint(prog.loops.size());
}

void add_final_assertion(danger_programt &prog,
    const goto_programt::targett &loop_end)
{
  goto_programt &body=get_danger_body(prog.gf);
  goto_programt::targett assertion=body.insert_after(loop_end);
  assertion->type=goto_program_instruction_typet::ASSERT;
  assertion->source_location=default_danger_source_location();
  assertion->guard=false_exprt();
}
}

void danger_add_learned_counterexamples(danger_programt &prog,
    const counterexamplest &ces)
{
  if (ces.empty()) return;
  array_valuest vals;
  const counterexamplet &prototype=*ces.begin();
  const size_t ces_count=ces.size();
  const create_x_array_valuest create_values(vals, prototype, ces_count);
  std::for_each(ces.begin(), ces.end(), create_values);
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt::targett pos=prog.danger_range.begin;
  declare_x_arrays(st, gf, --pos, vals);
  const goto_programt::targett loop_end=add_ce_loop(prog, ces.size());
  assign_ce_values(prog, prototype);
  create_constraints(prog);
  add_final_assertion(prog, loop_end);
}
