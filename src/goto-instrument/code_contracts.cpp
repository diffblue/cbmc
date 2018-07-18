/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#include "code_contracts.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_iterator.h>
#include <util/fresh_symbol.h>
#include <util/make_unique.h>
#include <util/replace_symbol.h>

#include <goto-programs/remove_skip.h>

#include <analyses/goto_rw.h>

#include <linking/static_lifetime_init.h>

#include <pointer-analysis/value_set_analysis_fi.h>

#include "loop_utils.h"

enum class contract_opst { APPLY, CHECK };

class code_contractst
{
public:
  code_contractst(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions):
      ns(_symbol_table),
      symbol_table(_symbol_table),
      goto_functions(_goto_functions)
  {
  }

  void operator()(contract_opst op_type);

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  void apply_code_contracts();
  void check_code_contracts();

  void code_contracts(goto_functionst::goto_functiont &goto_function);

  /// Applies (but does not check) a function contract.
  /// This will assume that the contract holds, and then use that assumption
  /// to remove the function call located at target.
  /// \param goto_program The goto program containing the target callsite.
  /// \param value_sets A value_setst object containing information about
  ///   aliasing in the goto program being analyzed
  /// \param target An iterator pointing to the function call to be removed.
  void apply_contract(
    goto_programt &goto_program,
    value_setst &value_sets,
    goto_programt::targett target);

  /// Applies (but does not check) a loop invariant.
  /// This will assume that the loop invariant is indeed an invariant, and then
  /// use that assumption to remove the loop.
  /// \param goto_function The goto function containing the target loop.
  /// \param value_sets A value_setst object containing information about
  ///   aliasing in the goto program being analyzed
  /// \param loop_head An iterator pointing to the first instruction of the
  ///   target loop.
  /// \param loop The loop being removed.
  void apply_invariant(
    goto_functionst::goto_functiont &goto_function,
    value_setst &value_sets,
    const goto_programt::targett loop_head,
    const loopt &loop);

  /// Checks (but does not apply) a function contract.
  /// This will build a code snippet to be inserted at dest which will check
  //    that the function contract is satisfied.
  /// \param function_id The id of the function being checked.
  /// \param goto_function The goto_function object for the function
  ///   being checked.
  /// \param dest An iterator pointing to the place to insert checking code.
  void check_contract(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function,
    goto_programt &dest);

  /// Checks and applies a loop invariant
  /// This will replace the loop with a code snippet (based on the loop) which
  ///   will check that the loop invariant is indeed ian invariant, and then
  ///   use that invariant in what follows.
  /// \param goto_function The goto function containing the target loop.
  /// \param value_sets A value_setst object containing information about
  ///   aliasing in the goto program being analyzed
  /// \param loop_head An iterator pointing to the first instruction of the
  ///   target loop.
  /// \param loop The loop being removed.
 void check_apply_invariant(
    goto_functionst::goto_functiont &goto_function,
    value_setst &value_sets,
    const goto_programt::targett loop_head,
    const loopt &loop);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location);
};

void code_contractst::apply_contract(
  goto_programt &goto_program,
  value_setst &value_sets,
  goto_programt::targett target)
{
  const code_function_callt &call=to_code_function_call(target->code);
  // we don't handle function pointers
  if(call.function().id()!=ID_symbol)
    return;

  const irep_idt &function=
    to_symbol_expr(call.function()).get_identifier();
  const symbolt &f_sym=ns.lookup(function);
  const code_typet &type=to_code_type(f_sym.type);

  exprt requires =
    static_cast<const exprt&>(type.find(ID_C_spec_requires));
  exprt ensures =
    static_cast<const exprt&>(type.find(ID_C_spec_ensures));

  if(ensures.is_nil())
  {
    // If there is no contract at all, we skip this function.
    if(requires.is_nil())
    {
      return;
    }
    else
    {
      // If there's no ensures but is a requires, treat it as ensures(true)
      ensures = true_exprt();
    }
  }

  // find out what can be written by the function
  modifiest modifies;

  rw_range_set_value_sett rw_set(ns, value_sets);
  goto_rw(goto_functions, function, rw_set);
  forall_rw_range_set_w_objects(it, rw_set)
  {
    // Skip over local variables of the function being called, as well as
    // variables not in the namespace (e.g. symex::invalid_object)
    const symbolt *symbol_ptr;
    if(!ns.lookup(it->first, symbol_ptr))
    {
      const std::string &name_string = id2string(symbol_ptr->name);
      std::string scope_prefix(id2string(ns.lookup(function).name));
      scope_prefix += "::";

      if(name_string.find(scope_prefix) == std::string::npos)
      {
        modifies.insert(ns.lookup(it->first).symbol_expr());
      }
    }
  }

  // build the havocking code
  goto_programt havoc_code;
  build_havoc_code(target, modifies, havoc_code);

  // replace formal parameters by arguments, replace return
  replace_symbolt replace;

  // TODO: return value could be nil
  if(type.return_type()!=empty_typet())
  {
    replace.insert("__CPROVER_return_value", call.lhs());
  }

  // formal parameters
  code_function_callt::argumentst::const_iterator a_it=
    call.arguments().begin();
  for(code_typet::parameterst::const_iterator
      p_it=type.parameters().begin();
      p_it!=type.parameters().end() &&
      a_it!=call.arguments().end();
      ++p_it, ++a_it)
    if(!p_it->get_identifier().empty())
      replace.insert(p_it->get_identifier(), *a_it);

  replace(requires);
  replace(ensures);

  // Havoc the return value of the function call.
  if(type.return_type()!=empty_typet())
  {
    const exprt &lhs = call.lhs();
    const exprt &rhs = side_effect_expr_nondett(call.lhs().type());
    target->make_assignment(code_assignt(lhs, rhs));
  }
  else
  {
    target->make_skip();
  }

  if(requires.is_not_nil())
  {
    goto_programt::instructiont a(ASSERT);
    a.guard=requires;
    a.function=target->function;
    a.source_location=target->source_location;

    goto_program.insert_before_swap(target, a);
    ++target;
  }

  goto_program.destructive_insert(target, havoc_code);

  {
    goto_programt::targett a=goto_program.insert_after(target);
    a->make_assumption(ensures);
    a->function=target->function;
    a->source_location=target->source_location;
  }
}

void code_contractst::apply_invariant(
  goto_functionst::goto_functiont &goto_function,
  value_setst &value_sets,
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  PRECONDITION(!loop.empty());

  // find the last back edge
  goto_programt::targett loop_end=loop_head;
  for(const goto_programt::targett &inst : loop)
  {
    if(inst->is_goto() &&
       inst->get_target()==loop_head &&
       inst->location_number>loop_end->location_number)
    {
      loop_end=inst;
    }
  }

  exprt invariant = static_cast<const exprt&>(
    loop_end->guard.find(ID_C_spec_loop_invariant));
  if(invariant.is_nil())
  {
    return;
  }

  // change H: loop; E: ...
  // to
  // H: assert(invariant);
  // havoc;
  // assume(invariant);
  // assume(!guard);
  // E: ...

  // find out what can get changed in the loop
  modifiest modifies;

  rw_range_set_value_sett rw_set(ns, value_sets);
  for(const goto_programt::targett &inst : loop)
  {
    goto_rw(inst, rw_set);
  }
  forall_rw_range_set_w_objects(it, rw_set)
  {
    const symbolt *symbol_ptr;
    if(!ns.lookup(it->first, symbol_ptr))
    {
      modifies.insert(ns.lookup(it->first).symbol_expr());
    }
  }

  // build the havocking code
  goto_programt havoc_code;

  // assert the invariant
  {
    goto_programt::targett a=havoc_code.add_instruction(ASSERT);
    a->guard=invariant;
    a->function=loop_head->function;
    a->source_location=loop_head->source_location;
    a->source_location.set_comment("Loop invariant violated before entry");
  }

  // havoc variables being written to
  build_havoc_code(loop_head, modifies, havoc_code);

  // assume the invariant
  {
    goto_programt::targett assume=havoc_code.add_instruction(ASSUME);
    assume->guard=invariant;
    assume->function=loop_head->function;
    assume->source_location=loop_head->source_location;
  }

  // assume !guard
  {
    goto_programt::targett assume = havoc_code.add_instruction(ASSUME);
    if(loop_head->is_goto())
    {
      assume->guard = loop_head->guard;
    }
    else
    {
      assume->guard = loop_end->guard;
      assume->guard.make_not();
    }
    assume->function = loop_head->function;
    assume->source_location = loop_head->source_location;
  }

  // Clear out loop body
  for(const goto_programt::targett &inst : loop)
  {
    inst->make_skip();
  }

  // Now havoc at the loop head. Use insert_before_swap to
  // preserve jumps to loop head.
  goto_function.body.insert_before_swap(loop_head, havoc_code);

  // Remove all the skips we created.
  remove_skip(goto_function.body);
}

void code_contractst::check_contract(
  const irep_idt &function_id,
  goto_functionst::goto_functiont &goto_function,
  goto_programt &dest)
{
  PRECONDITION(!dest.instructions.empty());

  exprt requires =
    static_cast<const exprt&>(goto_function.type.find(ID_C_spec_requires));
  exprt ensures =
    static_cast<const exprt&>(goto_function.type.find(ID_C_spec_ensures));

  // Nothing to check if ensures is nil.
  if(ensures.is_nil())
  {
    return;
  }

  // We build the following checking code:
  // if(nondet) goto end
  //   decl ret
  //   decl parameter1 ...
  //   assume(requires)  [optional]
  //   ret = function(parameter1, ...)
  //   assert(ensures)
  // end:
  //   skip

  // build skip so that if(nondet) can refer to it
  goto_programt tmp_skip;
  goto_programt::targett skip=tmp_skip.add_instruction(SKIP);
  skip->function=dest.instructions.front().function;
  skip->source_location=ensures.source_location();

  goto_programt check;

  // if(nondet)
  goto_programt::targett g=check.add_instruction();
  g->make_goto(skip, side_effect_expr_nondett(bool_typet()));
  g->function=skip->function;
  g->source_location=skip->source_location;

  // prepare function call including all declarations
  code_function_callt call;
  call.function()=ns.lookup(function_id).symbol_expr();
  replace_symbolt replace;

  // decl ret
  // TODO: Handle void functions
  // void functions seem to be handled by goto-cc
  if(goto_function.type.return_type()!=empty_typet())
  {
    goto_programt::targett d=check.add_instruction(DECL);
    d->function=skip->function;
    d->source_location=skip->source_location;

    symbol_exprt r=
      new_tmp_symbol(goto_function.type.return_type(),
                     d->source_location).symbol_expr();
    d->code=code_declt(r);

    call.lhs()=r;

    replace.insert("__CPROVER_return_value", r);
  }

  // decl parameter1 ...
  for(const auto &p_it : goto_function.type.parameters())
  {
    goto_programt::targett d=check.add_instruction(DECL);
    d->function=skip->function;
    d->source_location=skip->source_location;

    symbol_exprt p=
      new_tmp_symbol(p_it.type(), d->source_location).symbol_expr();
    d->code=code_declt(p);

    call.arguments().push_back(p);

    if(!p_it.get_identifier().empty())
      replace.insert(p_it.get_identifier(), p);
  }

  // rewrite any use of parameters
  replace(requires);
  replace(ensures);

  // assume(requires)
  if(requires.is_not_nil())
  {
    goto_programt::targett a=check.add_instruction();
    a->make_assumption(requires);
    a->function=skip->function;
    a->source_location=requires.source_location();
  }

  // ret=function(parameter1, ...)
  goto_programt::targett f=check.add_instruction();
  f->make_function_call(call);
  f->function=skip->function;
  f->source_location=skip->source_location;

  // assert(ensures)
  goto_programt::targett a=check.add_instruction();
  a->make_assertion(ensures);
  a->function=skip->function;
  a->source_location=ensures.source_location();

  // prepend the new code to dest
  check.destructive_append(tmp_skip);
  dest.destructive_insert(dest.instructions.begin(), check);
}

void code_contractst::check_apply_invariant(
  goto_functionst::goto_functiont &goto_function,
  value_setst &value_sets,
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  PRECONDITION(!loop.empty());

  // find the last back edge
  goto_programt::targett loop_end=loop_head;
  for(const goto_programt::targett &inst : loop)
    if(inst->is_goto() &&
       inst->get_target()==loop_head &&
       inst->location_number>loop_end->location_number)
      loop_end=inst;

  // see whether we have an invariant
  exprt invariant=
    static_cast<const exprt&>(
      loop_end->guard.find(ID_C_spec_loop_invariant));
  if(invariant.is_nil())
  {
    return;
  }

  // change H: loop; E: ...
  // to
  // H: assert(invariant);
  // havoc writes of loop;
  // assume(invariant);
  // loop (minus the ending goto);
  // assert(invariant);
  // assume(!guard)
  // E:
  // ...

  // find out what can get changed in the loop
  modifiest modifies;

  rw_range_set_value_sett rw_set(ns, value_sets);
  for(const goto_programt::targett &inst : loop)
  {
    goto_rw(inst, rw_set);
  }
  forall_rw_range_set_w_objects(it, rw_set)
  {
    const symbolt *symbol_ptr;
    if(!ns.lookup(it->first, symbol_ptr))
    {
      modifies.insert(ns.lookup(it->first).symbol_expr());
    }
  }

  // build the havocking code
  goto_programt havoc_code;

  // assert the invariant
  {
    goto_programt::targett a=havoc_code.add_instruction(ASSERT);
    a->guard=invariant;
    a->function=loop_head->function;
    a->source_location=loop_head->source_location;
    a->source_location.set_comment("Loop invariant violated before entry");
  }

  // havoc variables that can be modified by the loop
  build_havoc_code(loop_head, modifies, havoc_code);

  // assume the invariant
  {
    goto_programt::targett assume=havoc_code.add_instruction(ASSUME);
    assume->guard=invariant;
    assume->function=loop_head->function;
    assume->source_location=loop_head->source_location;
  }

  // assert the invariant at the end of the loop body
  {
    goto_programt::instructiont a(ASSERT);
    a.guard=invariant;
    a.function=loop_end->function;
    a.source_location=loop_end->source_location;
    a.source_location.set_comment("Loop invariant not preserved");

    goto_function.body.insert_before_swap(loop_end, a);
    ++loop_end;
  }

  // change the back edge into assume(!guard)
  loop_end->targets.clear();
  loop_end->type=ASSUME;
  if(loop_head->is_goto())
  {
    loop_end->guard = loop_head->guard;
  }
  else
  {
    loop_end->guard.make_not();
  }

  // Now havoc at the loop head. Use insert_before_swap to
  // preserve jumps to loop head.
  goto_function.body.insert_before_swap(loop_head, havoc_code);
}

const symbolt &code_contractst::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location)
{
  return get_fresh_aux_symbol(
    type,
    id2string(source_location.get_function()),
    "tmp_cc",
    source_location,
    ID_C,
    symbol_table);
}

{
  auto vs = util_make_unique<value_set_analysis_fit>(ns);
  (*vs)(goto_functions);
  std::unique_ptr<value_setst> value_sets = std::move(vs);

  Forall_goto_functions(it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function = it->second;

    natural_loops_mutablet natural_loops(goto_function.body);

    for(const auto &l_it : natural_loops.loop_map)
    {
      apply_invariant(goto_function,
                      *value_sets,
                      l_it.first,
                      l_it.second);
    }

    Forall_goto_program_instructions(it, goto_function.body)
    {
      if(it->is_function_call())
      {
        apply_contract(goto_function.body, *value_sets, it);
      }
    }
  }

  goto_functions.update();
}

void code_contractst::check_code_contracts()
{
  auto vs = util_make_unique<value_set_analysis_fit>(ns);
  (*vs)(goto_functions);
  std::unique_ptr<value_setst> value_sets = std::move(vs);

  goto_functionst::function_mapt::iterator i_it=
    goto_functions.function_map.find(INITIALIZE_FUNCTION);
  CHECK_RETURN(i_it!=goto_functions.function_map.end());
  goto_programt &init_function = i_it->second.body;

  Forall_goto_functions(it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function = it->second;

    natural_loops_mutablet natural_loops(goto_function.body);

    for(const auto &l_it : natural_loops.loop_map)
    {
      check_apply_invariant(goto_function,
                            *value_sets,
                            l_it.first,
                            l_it.second);
    }

    Forall_goto_program_instructions(it, goto_function.body)
    {
      if(it->is_function_call())
      {
        apply_contract(goto_function.body, *value_sets, it);
      }
    }
  }

  Forall_goto_functions(it, goto_functions)
  {
    check_contract(it->first, it->second, init_function);
  }

  // Partially initialize state
  goto_programt init_code;

  goto_programt::targett d = init_code.add_instruction(DECL);
  d->function = i_it->first;
  // TODO add source location
  // d->source_location =

  symbol_exprt tmp_var =
    new_tmp_symbol(void_typet(), d->source_location).symbol_expr();
  d->code = code_declt(tmp_var);
  d->code.add_source_location() = d->source_location;

  {
    const symbol_exprt &deallocated_expr =
      ns.lookup(CPROVER_PREFIX "deallocated").symbol_expr();

    goto_programt::targett a = init_code.add_instruction(ASSIGN);
    a->function = i_it->first;
    // TODO add source location
    // a->source_location =
    address_of_exprt rhs(tmp_var, to_pointer_type(deallocated_expr.type()));
    a->code = code_assignt(deallocated_expr, rhs);
    a->code.add_source_location() = a->source_location;
  }

  {
    const symbol_exprt &dead_expr =
      ns.lookup(CPROVER_PREFIX "dead_object").symbol_expr();

    goto_programt::targett a = init_code.add_instruction(ASSIGN);
    a->function = i_it->first;
    // TODO add source location
    // a->source_location =
    address_of_exprt rhs(tmp_var, to_pointer_type(dead_expr.type()));
    a->code = code_assignt(dead_expr, rhs);
    a->code.add_source_location() = a->source_location;
  }

  init_function.destructive_insert(init_function.instructions.begin(),
                                   init_code);

  remove_skip(init_function);

  goto_functions.update();
}

void code_contractst::operator()(contract_opst op_type)
{
  switch(op_type)
  {
    case contract_opst::APPLY:
      apply_code_contracts();
      break;
    case contract_opst::CHECK:
      check_code_contracts();
      break;
  }
}

void check_code_contracts(goto_modelt &goto_model)
{
  code_contractst(goto_model.symbol_table, goto_model.goto_functions)
    (contract_opst::CHECK);
}

void apply_code_contracts(goto_modelt &goto_model)
{
  code_contractst(goto_model.symbol_table, goto_model.goto_functions)
    (contract_opst::APPLY);
}
