/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#include "code_contracts.h"

#include <util/fresh_symbol.h>
#include <util/replace_symbol.h>

#include <goto-programs/remove_skip.h>

#include <analyses/local_may_alias.h>

#include <linking/static_lifetime_init.h>

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

  void apply_contract(
    goto_programt &goto_program,
    goto_programt::targett target);

  void apply_invariant(
    goto_functionst::goto_functiont &goto_function,
    const local_may_aliast &local_may_alias,
    const goto_programt::targett loop_head,
    const loopt &loop);

  void check_contract(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function,
    goto_programt &dest);

  void check_apply_invariant(
    goto_functionst::goto_functiont &goto_function,
    const local_may_aliast &local_may_alias,
    const goto_programt::targett loop_head,
    const loopt &loop);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location);
};

void code_contractst::apply_contract(
  goto_programt &goto_program,
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

  // replace formal parameters by arguments, replace return
  replace_symbolt replace;

  // TODO: return value could be nil
  if(type.return_type()!=empty_typet())
    replace.insert("__CPROVER_return_value", call.lhs());

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

  if(requires.is_not_nil())
  {
    goto_programt::instructiont a(ASSERT);
    a.guard=requires;
    a.function=target->function;
    a.source_location=target->source_location;

    goto_program.insert_before_swap(target, a);
    ++target;
  }
  // TODO: Havoc write set of the function between assert and ensure.

  target->make_assumption(ensures);
}

void code_contractst::apply_invariant(
  goto_functionst::goto_functiont &goto_function,
  const local_may_aliast &local_may_alias,
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  assert(!loop.empty());

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

  // TODO: Allow for not havocking in the for/while case

  // change H: loop; E: ...
  // to
  // H: assert(invariant);
  // havoc;
  // assume(invariant);
  // assume(!guard);
  // E: ...

  // find out what can get changed in the loop
  modifiest modifies;
  get_modifies(local_may_alias, loop, modifies);

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
  // TODO: consider breaks and how they're implemented.
  // TODO: Also consider continues and whether they jump to loop end or head
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

  // Now havoc at the loop head. Use insert_swap to
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
  assert(!dest.instructions.empty());

  exprt requires =
    static_cast<const exprt&>(goto_function.type.find(ID_C_spec_requires));
  exprt ensures =
    static_cast<const exprt&>(goto_function.type.find(ID_C_spec_ensures));

  // Nothing to check if ensures is nil.
  if(ensures.is_nil()) {
    return;
  }

  // build:
  // if(nondet)
  //   decl ret
  //   decl parameter1 ...
  //   assume(requires)  [optional]
  //   ret = function(parameter1, ...)
  //   assert(ensures)

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

  // assume(requires)
  if(requires.is_not_nil())
  {
    goto_programt::targett a=check.add_instruction();
    a->make_assumption(requires);
    a->function=skip->function;
    a->source_location=requires.source_location();

    // rewrite any use of parameters
    replace(a->guard);
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

  // rewrite any use of __CPROVER_return_value
  replace(a->guard);

  // prepend the new code to dest
  check.destructive_append(tmp_skip);
  dest.destructive_insert(dest.instructions.begin(), check);
}

void code_contractst::check_apply_invariant(
  goto_functionst::goto_functiont &goto_function,
  const local_may_aliast &local_may_alias,
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  assert(!loop.empty());

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
    return;

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
  get_modifies(local_may_alias, loop, modifies);

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

  // Now havoc at the loop head. Use insert_swap to
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

void code_contractst::apply_code_contracts()
{
  Forall_goto_functions(it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function = it->second;

    // TODO: This aliasing check is insufficiently strong, in general.
    local_may_aliast local_may_alias(goto_function);
    natural_loops_mutablet natural_loops(goto_function.body);

    for(const auto &l_it : natural_loops.loop_map)
    {
      apply_invariant(goto_function,
                      local_may_alias,
                      l_it.first,
                      l_it.second);
    }

    Forall_goto_program_instructions(it, goto_function.body)
    {
      if(it->is_function_call())
      {
        apply_contract(goto_function.body, it);
      }
    }
  }

  goto_functions.update();
}

void code_contractst::check_code_contracts()
{
  goto_functionst::function_mapt::iterator i_it=
    goto_functions.function_map.find(INITIALIZE_FUNCTION);
  assert(i_it!=goto_functions.function_map.end());

  Forall_goto_functions(it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function = it->second;

    // TODO: This aliasing check is insufficiently strong, in general.
    local_may_aliast local_may_alias(goto_function);
    natural_loops_mutablet natural_loops(goto_function.body);

    for(const auto &l_it : natural_loops.loop_map)
    {
      check_apply_invariant(goto_function,
                            local_may_alias,
                            l_it.first,
                            l_it.second);
    }

    Forall_goto_program_instructions(it, goto_function.body)
    {
      if(it->is_function_call())
      {
        apply_contract(goto_function.body, it);
      }
    }
  }

  Forall_goto_functions(it, goto_functions)
  {
    check_contract(it->first, it->second, i_it->second.body);
  }

  // remove skips
  remove_skip(i_it->second.body);

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
