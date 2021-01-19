/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#include <algorithm>
#include <unordered_set>

#include <analyses/local_may_alias.h>

#include <goto-programs/remove_skip.h>

#include <linking/static_lifetime_init.h>

#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/replace_symbol.h>

#include "code_contracts.h"
#include "loop_utils.h"

/// Predicate to be used with the exprt::visit() function. The function
/// found_return_value() will return `true` iff this predicate is called on an
/// expr that contains `__CPROVER_return_value`.
class return_value_visitort : public const_expr_visitort
{
public:
  return_value_visitort() : const_expr_visitort()
  {
  }

  // \brief Has this object been passed to exprt::visit() on an exprt whose
  //        descendants contain __CPROVER_return_value?
  bool found_return_value()
  {
    return found;
  }

  void operator()(const exprt &exp) override
  {
    if(exp.id() != ID_symbol)
      return;
    const symbol_exprt &sym = to_symbol_expr(exp);
    found |= sym.get_identifier() == CPROVER_PREFIX "return_value";
  }

protected:
  bool found;
};

static void check_apply_invariants(
  goto_functionst::goto_functiont &goto_function,
  const local_may_aliast &local_may_alias,
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  PRECONDITION(!loop.empty());

  // find the last back edge
  goto_programt::targett loop_end=loop_head;
  for(loopt::const_iterator
      it=loop.begin();
      it!=loop.end();
      ++it)
    if((*it)->is_goto() &&
       (*it)->get_target()==loop_head &&
       (*it)->location_number>loop_end->location_number)
      loop_end=*it;

  // see whether we have an invariant
  exprt invariant = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_loop_invariant));
  if(invariant.is_nil())
    return;

  // change H: loop; E: ...
  // to
  // H: assert(invariant);
  // havoc;
  // assume(invariant);
  // if(guard) goto E:
  // loop;
  // assert(invariant);
  // assume(false);
  // E: ...

  // find out what can get changed in the loop
  modifiest modifies;
  get_modifies(local_may_alias, loop, modifies);

  // build the havocking code
  goto_programt havoc_code;

  // assert the invariant
  {
    goto_programt::targett a = havoc_code.add(
      goto_programt::make_assertion(invariant, loop_head->source_location));
    a->source_location.set_comment("Loop invariant violated before entry");
  }

  // havoc variables being written to
  build_havoc_code(loop_head, modifies, havoc_code);

  // assume the invariant
  havoc_code.add(
    goto_programt::make_assumption(invariant, loop_head->source_location));

  // non-deterministically skip the loop if it is a do-while loop
  if(!loop_head->is_goto())
  {
    havoc_code.add(goto_programt::make_goto(
      loop_end,
      side_effect_expr_nondett(bool_typet(), loop_head->source_location)));
  }

  // Now havoc at the loop head. Use insert_swap to
  // preserve jumps to loop head.
  goto_function.body.insert_before_swap(loop_head, havoc_code);

  // assert the invariant at the end of the loop body
  {
    goto_programt::instructiont a =
      goto_programt::make_assertion(invariant, loop_end->source_location);
    a.source_location.set_comment("Loop invariant not preserved");
    goto_function.body.insert_before_swap(loop_end, a);
    ++loop_end;
  }

  // change the back edge into assume(false) or assume(guard)
  loop_end->targets.clear();
  loop_end->type=ASSUME;
  if(loop_head->is_goto())
    loop_end->set_condition(false_exprt());
  else
    loop_end->set_condition(boolean_negate(loop_end->get_condition()));
}

bool code_contractst::has_contract(const irep_idt fun_name)
{
  const symbolt &function_symbol = ns.lookup(fun_name);
  const code_typet &type = to_code_type(function_symbol.type);
  if(type.find(ID_C_spec_assigns).is_not_nil())
    return true;

  return type.find(ID_C_spec_requires).is_not_nil() ||
         type.find(ID_C_spec_ensures).is_not_nil();
}

bool code_contractst::apply_contract(
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const code_function_callt &call = target->get_function_call();

  // Return if the function is not named in the call; currently we don't handle
  // function pointers.
  // TODO: handle function pointers.
  if(call.function().id() != ID_symbol)
    return false;

  // Retrieve the function type, which is needed to extract the contract
  // components.
  const irep_idt &function = to_symbol_expr(call.function()).get_identifier();
  const symbolt &function_symbol = ns.lookup(function);
  const code_typet &type = to_code_type(function_symbol.type);

  // Isolate each component of the contract.
  exprt assigns = static_cast<const exprt &>(type.find(ID_C_spec_assigns));
  exprt requires = static_cast<const exprt &>(type.find(ID_C_spec_requires));
  exprt ensures = static_cast<const exprt &>(type.find(ID_C_spec_ensures));

  // Check to see if the function  contract actually constrains its effect on
  // the program state; if not, return.
  if(ensures.is_nil() && assigns.is_nil())
    return false;

  // Create a replace_symbolt object, for replacing expressions in the callee
  // with expressions from the call site (e.g. the return value).
  replace_symbolt replace;
  if(type.return_type() != empty_typet())
  {
    // Check whether the function's return value is not disregarded.
    if(call.lhs().is_not_nil())
    {
      // If so, have it replaced appropriately.
      // For example, if foo() ensures that its return value is > 5, then
      // rewrite calls to foo as follows:
      // x = foo() -> assume(__CPROVER_return_value > 5) -> assume(x > 5)
      symbol_exprt ret_val(CPROVER_PREFIX "return_value", call.lhs().type());
      replace.insert(ret_val, call.lhs());
    }
    else
    {
      // If the function does return a value, but the return value is
      // disregarded, check if the postcondition includes the return value.
      return_value_visitort v;
      ensures.visit(v);
      if(v.found_return_value())
      {
        // The postcondition does mention __CPROVER_return_value, so mint a
        // fresh variable to replace __CPROVER_return_value with.
        const symbolt &fresh = get_fresh_aux_symbol(
          type.return_type(),
          id2string(function),
          "ignored_return_value",
          call.source_location(),
          symbol_table.lookup_ref(function).mode,
          ns,
          symbol_table);
        symbol_exprt ret_val(CPROVER_PREFIX "return_value", type.return_type());
        replace.insert(ret_val, fresh.symbol_expr());
      }
    }
  }

  // Replace formal parameters
  code_function_callt::argumentst::const_iterator a_it=
    call.arguments().begin();
  for(code_typet::parameterst::const_iterator p_it = type.parameters().begin();
      p_it != type.parameters().end() && a_it != call.arguments().end();
      ++p_it, ++a_it)
  {
    if(!p_it->get_identifier().empty())
    {
      symbol_exprt p(p_it->get_identifier(), p_it->type());
      replace.insert(p, *a_it);
    }
  }

  // Replace expressions in the contract components.
  replace(assigns);
  replace(requires);
  replace(ensures);

  // Insert assertion of the precondition immediately before the call site.
  if(requires.is_not_nil())
  {
    goto_programt::instructiont a =
      goto_programt::make_assertion(requires, target->source_location);

    goto_program.insert_before_swap(target, a);
    ++target;
  }

  // Create a series of non-deterministic assignments to havoc the variables
  // in the assigns clause.
  if(assigns.is_not_nil())
  {
    goto_programt assigns_havoc;
    modifiest assigns_tgts;
    const exprt::operandst &targets = assigns.operands();
    for(const exprt &curr_op : targets)
    {
      if(curr_op.id() == ID_symbol || curr_op.id() == ID_dereference)
      {
        assigns_tgts.insert(curr_op);
      }
      else
      {
        log.error() << "Unable to apply assigns clause for expression of type '"
                    << curr_op.id() << "'; not enforcing assigns clause."
                    << messaget::eom;
        return true;
      }
    }
    build_havoc_code(target, assigns_tgts, assigns_havoc);

    // Insert the non-deterministic assignment immediately before the call site.
    goto_program.insert_before_swap(target, assigns_havoc);
    std::advance(target, assigns_tgts.size());
  }

  // To remove the function call, replace it with an assumption statement
  // assuming the postcondition, if there is one. Otherwise, replace the
  // function call with a SKIP statement.
  if(ensures.is_not_nil())
  {
    *target = goto_programt::make_assumption(ensures, target->source_location);
  }
  else
  {
    *target = goto_programt::make_skip();
  }

  // Add this function to the set of replaced functions.
  summarized.insert(function);
  return false;
}

void code_contractst::code_contracts(
  goto_functionst::goto_functiont &goto_function)
{
  local_may_aliast local_may_alias(goto_function);
  natural_loops_mutablet natural_loops(goto_function.body);

  // iterate over the (natural) loops in the function
  for(natural_loops_mutablet::loop_mapt::const_iterator l_it =
        natural_loops.loop_map.begin();
      l_it != natural_loops.loop_map.end();
      l_it++)
    check_apply_invariants(
      goto_function, local_may_alias, l_it->first, l_it->second);

  // look at all function calls
  Forall_goto_program_instructions(ins, goto_function.body)
    if(ins->is_function_call())
      apply_contract(goto_function.body, ins);
}

const symbolt &code_contractst::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location,
  const irep_idt &function_id,
  const irep_idt &mode)
{
  return get_fresh_aux_symbol(
    type,
    id2string(function_id) + "::tmp_cc",
    "tmp_cc",
    source_location,
    mode,
    symbol_table);
}

static exprt create_alias_expression(
  const exprt &assigns,
  const exprt &lhs,
  std::vector<exprt> &aliasable_references)
{
  bool first_iter = true;
  exprt running = false_exprt();
  for(auto aliasable : aliasable_references)
  {
    exprt left_ptr = address_of_exprt{lhs};
    exprt right_ptr = aliasable;
    exprt same = same_object(left_ptr, right_ptr);

    if(first_iter)
    {
      running = same;
      first_iter = false;
    }
    else
    {
      exprt::operandst disjuncts;
      disjuncts.push_back(same);
      disjuncts.push_back(running);
      running = disjunction(disjuncts);
    }
  }

  return running;
}

void code_contractst::populate_assigns_references(
  const symbolt &function_symbol,
  const irep_idt &function_id,
  goto_programt &created_decls,
  std::vector<exprt> &created_references)
{
  const code_typet &type = to_code_type(function_symbol.type);
  const exprt &assigns =
    static_cast<const exprt &>(type.find(ID_C_spec_assigns));

  const exprt::operandst &targets = assigns.operands();
  for(const exprt &curr_op : targets)
  {
    // Declare a new symbol to stand in for the reference
    symbol_exprt standin = new_tmp_symbol(
                             pointer_type(curr_op.type()),
                             function_symbol.location,
                             function_id,
                             function_symbol.mode)
                             .symbol_expr();

    created_decls.add(
      goto_programt::make_decl(standin, function_symbol.location));

    created_decls.add(goto_programt::make_assignment(
      code_assignt(standin, std::move(address_of_exprt{curr_op})),
      function_symbol.location));

    // Add a map entry from the original operand to the new symbol
    created_references.push_back(standin);
  }
}

void code_contractst::instrument_assigns_statement(
  goto_programt::instructionst::iterator &instruction_iterator,
  goto_programt &program,
  exprt &assigns,
  std::vector<exprt> &assigns_references,
  std::set<exprt> &freely_assignable_exprs)
{
  INVARIANT(
    instruction_iterator->is_assign(),
    "The first argument of instrument_assigns_statement should always be"
    " an assignment");
  const exprt &lhs = instruction_iterator->get_assign().lhs();
  if(freely_assignable_exprs.find(lhs) != freely_assignable_exprs.end())
  {
    return;
  }
  exprt alias_expr = create_alias_expression(assigns, lhs, assigns_references);

  goto_programt alias_assertion;
  alias_assertion.add(goto_programt::make_assertion(
    alias_expr, instruction_iterator->source_location));
  program.insert_before_swap(instruction_iterator, alias_assertion);
  ++instruction_iterator;
}

void code_contractst::instrument_call_statement(
  goto_programt::instructionst::iterator &instruction_iterator,
  goto_programt &program,
  exprt &assigns,
  std::vector<exprt> &aliasable_references,
  std::set<exprt> &freely_assignable_exprs)
{
  INVARIANT(
    instruction_iterator->is_function_call(),
    "The first argument of instrument_call_statement should always be "
    "a function call");
  code_function_callt call = instruction_iterator->get_function_call();
  const irep_idt &called_name =
    to_symbol_expr(call.function()).get_identifier();

  // Malloc allocates memory which is not part of the caller's memory
  // frame, so we want to capture the newly-allocated memory and
  // treat it as assignable.
  if(called_name == "malloc")
  {
    aliasable_references.push_back(call.lhs());

    // Make the variable, where result of malloc is stored, freely assignable.
    goto_programt::instructionst::iterator local_instruction_iterator =
      instruction_iterator;
    local_instruction_iterator++;
    if(
      local_instruction_iterator->is_assign() &&
      local_instruction_iterator->get_assign().lhs().is_not_nil())
    {
      freely_assignable_exprs.insert(
        local_instruction_iterator->get_assign().lhs());
    }
    return; // assume malloc edits no currently-existing memory objects.
  }

  if(call.lhs().is_not_nil())
  {
    exprt alias_expr =
      create_alias_expression(assigns, call.lhs(), aliasable_references);

    goto_programt alias_assertion;
    alias_assertion.add(goto_programt::make_assertion(
      alias_expr, instruction_iterator->source_location));
    program.insert_before_swap(instruction_iterator, alias_assertion);
    ++instruction_iterator;
  }

  // TODO we don't handle function pointers
  if(call.function().id() == ID_symbol)
  {
    const symbolt &called_sym = ns.lookup(called_name);
    const code_typet &called_type = to_code_type(called_sym.type);

    auto called_func = goto_functions.function_map.find(called_name);
    if(called_func == goto_functions.function_map.end())
    {
      log.error() << "Could not find function '" << called_name
                  << "' in goto-program; not enforcing assigns clause."
                  << messaget::eom;
      return;
    }

    exprt called_assigns =
      static_cast<const exprt &>(called_sym.type.find(ID_C_spec_assigns));
    if(called_assigns.is_nil()) // Called function has no assigns clause
    {
      // Fail if called function has no assigns clause.
      log.error() << "No assigns specification found for function '"
                  << called_name
                  << "' in goto-program; not enforcing assigns clause."
                  << messaget::eom;

      // Create a false assertion, so the analysis will fail if this function
      // is called.
      goto_programt failing_assertion;
      failing_assertion.add(goto_programt::make_assertion(
        false_exprt(), instruction_iterator->source_location));
      program.insert_before_swap(instruction_iterator, failing_assertion);
      ++instruction_iterator;

      return;
    }
    else // Called function has assigns clause
    {
      replace_symbolt replace;
      // Replace formal parameters
      code_function_callt::argumentst::const_iterator a_it =
        call.arguments().begin();
      for(code_typet::parameterst::const_iterator p_it =
            called_type.parameters().begin();
          p_it != called_type.parameters().end() &&
          a_it != call.arguments().end();
          ++p_it, ++a_it)
      {
        if(!p_it->get_identifier().empty())
        {
          symbol_exprt p(p_it->get_identifier(), p_it->type());
          replace.insert(p, *a_it);
        }
      }

      replace(called_assigns);
      for(exprt::operandst::const_iterator called_op_it =
            called_assigns.operands().begin();
          called_op_it != called_assigns.operands().end();
          called_op_it++)
      {
        if(
          freely_assignable_exprs.find(*called_op_it) !=
          freely_assignable_exprs.end())
        {
          continue;
        }
        exprt alias_expr =
          create_alias_expression(assigns, *called_op_it, aliasable_references);

        goto_programt alias_assertion;
        alias_assertion.add(goto_programt::make_assertion(
          alias_expr, instruction_iterator->source_location));
        program.insert_before_swap(instruction_iterator, alias_assertion);
        ++instruction_iterator;
      }
    }
  }
}

bool code_contractst::check_for_looped_mallocs(const goto_programt &program)
{
  // Collect all GOTOs and mallocs
  std::vector<goto_programt::instructiont> back_gotos;
  std::vector<goto_programt::instructiont> malloc_calls;

  int idx = 0;
  for(goto_programt::instructiont instruction : program.instructions)
  {
    if(instruction.is_backwards_goto())
    {
      back_gotos.push_back(instruction);
    }
    if(instruction.is_function_call())
    {
      code_function_callt call = instruction.get_function_call();
      const irep_idt &called_name =
        to_symbol_expr(call.function()).get_identifier();

      if(called_name == "malloc")
      {
        malloc_calls.push_back(instruction);
      }
    }
    idx++;
  }
  // Make sure there are no gotos that go back such that a malloc is between
  // the goto and its destination (possible loop).
  for(auto goto_entry : back_gotos)
  {
    for(const auto &target : goto_entry.targets)
    {
      for(auto malloc_entry : malloc_calls)
      {
        if(
          malloc_entry.location_number >= target->location_number &&
          malloc_entry.location_number < goto_entry.location_number)
        {
          // In order to statically keep track of all the memory we should
          //   be able to assign, we need to create ghost variables to store
          //   references to that memory.
          // If a malloc is in a loop, we can't generally determine how many
          //   times it will run in order to create an appropriate number of
          //   references for the assignable memory.
          // So, if we have a malloc in a loop, we can't statically create the
          //   assertion statements needed to enforce the assigns clause.
          log.error() << "Call to malloc at location "
                      << malloc_entry.location_number << " falls between goto "
                      << "source location " << goto_entry.location_number
                      << " and it's destination at location "
                      << target->location_number << ". "
                      << "Unable to complete instrumentation, as this malloc "
                      << "may be in a loop." << messaget::eom;
          throw 0;
        }
      }
    }
  }
  return false;
}

bool code_contractst::add_pointer_checks(const std::string &function_name)
{
  // Get the function object before instrumentation.
  auto old_function = goto_functions.function_map.find(function_name);
  if(old_function == goto_functions.function_map.end())
  {
    log.error() << "Could not find function '" << function_name
                << "' in goto-program; not enforcing contracts."
                << messaget::eom;
    return true;
  }
  goto_programt &program = old_function->second.body;
  if(program.instructions.empty()) // empty function body
  {
    return false;
  }

  const irep_idt function_id(function_name);
  const symbolt &function_symbol = ns.lookup(function_id);
  const code_typet &type = to_code_type(function_symbol.type);

  exprt assigns = static_cast<const exprt &>(type.find(ID_C_spec_assigns));

  // Return if there are no reference checks to perform.
  if(assigns.is_nil())
    return false;

  goto_programt::instructionst::iterator instruction_iterator =
    program.instructions.begin();

  // Create temporary variables to hold the assigns clause targets before
  // they can be modified.
  goto_programt standin_decls;
  std::vector<exprt> original_references;
  populate_assigns_references(
    function_symbol, function_id, standin_decls, original_references);

  // Create a list of variables that are okay to assign.
  std::set<exprt> freely_assignable_exprs;
  for(code_typet::parametert param : type.parameters())
  {
    freely_assignable_exprs.insert(param);
  }

  int lines_to_iterate = standin_decls.instructions.size();
  program.insert_before_swap(instruction_iterator, standin_decls);
  std::advance(instruction_iterator, lines_to_iterate);

  if(check_for_looped_mallocs(program))
  {
    return true;
  }

  // Insert aliasing assertions
  for(; instruction_iterator != program.instructions.end();
      ++instruction_iterator)
  {
    if(instruction_iterator->is_decl())
    {
      freely_assignable_exprs.insert(instruction_iterator->get_decl().symbol());
    }
    else if(instruction_iterator->is_assign())
    {
      instrument_assigns_statement(
        instruction_iterator,
        program,
        assigns,
        original_references,
        freely_assignable_exprs);
    }
    else if(instruction_iterator->is_function_call())
    {
      instrument_call_statement(
        instruction_iterator,
        program,
        assigns,
        original_references,
        freely_assignable_exprs);
    }
  }
  return false;
}

bool code_contractst::enforce_contract(const std::string &fun_to_enforce)
{
  // Add statements to the source function to ensure assigns clause is
  // respected.
  add_pointer_checks(fun_to_enforce);

  // Rename source function
  std::stringstream ss;
  ss << CPROVER_PREFIX << "contracts_original_" << fun_to_enforce;
  const irep_idt mangled(ss.str());
  const irep_idt original(fun_to_enforce);

  auto old_function = goto_functions.function_map.find(original);
  if(old_function == goto_functions.function_map.end())
  {
    log.error() << "Could not find function '" << fun_to_enforce
                << "' in goto-program; not enforcing contracts."
                << messaget::eom;
    return true;
  }

  std::swap(goto_functions.function_map[mangled], old_function->second);
  goto_functions.function_map.erase(old_function);

  // Place a new symbol with the mangled name into the symbol table
  source_locationt sl;
  sl.set_file("instrumented for code contracts");
  sl.set_line("0");
  symbolt mangled_sym;
  const symbolt *original_sym = symbol_table.lookup(original);
  mangled_sym = *original_sym;
  mangled_sym.name = mangled;
  mangled_sym.base_name = mangled;
  mangled_sym.location = sl;
  const auto mangled_found = symbol_table.insert(std::move(mangled_sym));
  INVARIANT(
    mangled_found.second,
    "There should be no existing function called " + ss.str() +
      " in the symbol table because that name is a mangled name");

  // Insert wrapper function into goto_functions
  auto nexist_old_function = goto_functions.function_map.find(original);
  INVARIANT(
    nexist_old_function == goto_functions.function_map.end(),
    "There should be no function called " + fun_to_enforce +
      " in the function map because that function should have had its"
      " name mangled");

  auto mangled_fun = goto_functions.function_map.find(mangled);
  INVARIANT(
    mangled_fun != goto_functions.function_map.end(),
    "There should be a function called " + ss.str() +
      " in the function map because we inserted a fresh goto-program"
      " with that mangled name");

  goto_functiont &wrapper = goto_functions.function_map[original];
  wrapper.parameter_identifiers = mangled_fun->second.parameter_identifiers;
  wrapper.body.add(goto_programt::make_end_function(sl));
  add_contract_check(original, mangled, wrapper.body);
  return false;
}

void code_contractst::add_contract_check(
  const irep_idt &wrapper_fun,
  const irep_idt &mangled_fun,
  goto_programt &dest)
{
  PRECONDITION(!dest.instructions.empty());

  const symbolt &function_symbol = ns.lookup(mangled_fun);
  const code_typet &code_type = to_code_type(function_symbol.type);

  const exprt &assigns =
    static_cast<const exprt &>(code_type.find(ID_C_spec_assigns));
  const exprt &requires =
    static_cast<const exprt &>(code_type.find(ID_C_spec_requires));
  const exprt &ensures =
    static_cast<const exprt &>(code_type.find(ID_C_spec_ensures));
  INVARIANT(
    ensures.is_not_nil() || assigns.is_not_nil(),
    "Code contract enforcement is trivial without an ensures or assigns "
    "clause.");

  // build:
  // if(nondet)
  //   decl ret
  //   decl parameter1 ...
  //   assume(requires)  [optional]
  //   ret=function(parameter1, ...)
  //   assert(ensures)
  // skip: ...

  // build skip so that if(nondet) can refer to it
  goto_programt tmp_skip;
  goto_programt::targett skip =
    tmp_skip.add(goto_programt::make_skip(ensures.source_location()));

  goto_programt check;

  // if(nondet)
  check.add(goto_programt::make_goto(
    skip,
    side_effect_expr_nondett(bool_typet(), skip->source_location),
    skip->source_location));

  // prepare function call including all declarations
  code_function_callt call(function_symbol.symbol_expr());
  replace_symbolt replace;

  // decl ret
  if(code_type.return_type() != empty_typet())
  {
    symbol_exprt r = new_tmp_symbol(
                       code_type.return_type(),
                       skip->source_location,
                       wrapper_fun,
                       function_symbol.mode)
                       .symbol_expr();
    check.add(goto_programt::make_decl(r, skip->source_location));

    call.lhs()=r;

    symbol_exprt ret_val(CPROVER_PREFIX "return_value", call.lhs().type());
    replace.insert(ret_val, r);
  }

  // decl parameter1 ...
  goto_functionst::function_mapt::iterator f_it =
    goto_functions.function_map.find(mangled_fun);
  PRECONDITION(f_it != goto_functions.function_map.end());

  const goto_functionst::goto_functiont &gf = f_it->second;
  for(const auto &parameter : gf.parameter_identifiers)
  {
    PRECONDITION(!parameter.empty());
    const symbolt &parameter_symbol = ns.lookup(parameter);

    symbol_exprt p = new_tmp_symbol(
                       parameter_symbol.type,
                       skip->source_location,
                       wrapper_fun,
                       parameter_symbol.mode)
                       .symbol_expr();
    check.add(goto_programt::make_decl(p, skip->source_location));

    call.arguments().push_back(p);

    replace.insert(parameter_symbol.symbol_expr(), p);
  }

  // assume(requires)
  if(requires.is_not_nil())
  {
    // rewrite any use of parameters
    exprt requires_cond = requires;
    replace(requires_cond);

    check.add(goto_programt::make_assumption(
      requires_cond, requires.source_location()));
  }

  // ret=mangled_fun(parameter1, ...)
  check.add(goto_programt::make_function_call(call, skip->source_location));

  // rewrite any use of __CPROVER_return_value
  exprt ensures_cond = ensures;
  replace(ensures_cond);

  // assert(ensures)
  if(ensures.is_not_nil())
  {
    check.add(
      goto_programt::make_assertion(ensures_cond, ensures.source_location()));
  }

  // prepend the new code to dest
  check.destructive_append(tmp_skip);
  dest.destructive_insert(dest.instructions.begin(), check);
}

bool code_contractst::replace_calls(
  const std::set<std::string> &funs_to_replace)
{
  bool fail = false;
  for(const auto &fun : funs_to_replace)
  {
    if(!has_contract(fun))
    {
      log.error() << "Function '" << fun
                  << "' does not have a contract; "
                     "not replacing calls with contract."
                  << messaget::eom;
      fail = true;
    }
  }
  if(fail)
    return true;

  for(auto &goto_function : goto_functions.function_map)
  {
    Forall_goto_program_instructions(ins, goto_function.second.body)
    {
      if(ins->is_function_call())
      {
        const code_function_callt &call = ins->get_function_call();

        // TODO we don't handle function pointers
        if(call.function().id() != ID_symbol)
          continue;

        const irep_idt &fun_name =
          to_symbol_expr(call.function()).get_identifier();
        auto found = std::find(
          funs_to_replace.begin(), funs_to_replace.end(), id2string(fun_name));
        if(found == funs_to_replace.end())
          continue;

        fail |= apply_contract(goto_function.second.body, ins);
      }
    }
  }

  if(fail)
    return true;

  for(auto &goto_function : goto_functions.function_map)
    remove_skip(goto_function.second.body);

  goto_functions.update();

  return false;
}

bool code_contractst::replace_calls()
{
  std::set<std::string> funs_to_replace;
  for(auto &goto_function : goto_functions.function_map)
  {
    if(has_contract(goto_function.first))
      funs_to_replace.insert(id2string(goto_function.first));
  }
  return replace_calls(funs_to_replace);
}

bool code_contractst::enforce_contracts()
{
  std::set<std::string> funs_to_enforce;
  for(auto &goto_function : goto_functions.function_map)
  {
    if(has_contract(goto_function.first))
      funs_to_enforce.insert(id2string(goto_function.first));
  }
  return enforce_contracts(funs_to_enforce);
}

bool code_contractst::enforce_contracts(
  const std::set<std::string> &funs_to_enforce)
{
  bool fail = false;
  for(const auto &fun : funs_to_enforce)
  {
    if(!has_contract(fun))
    {
      fail = true;
      log.error() << "Could not find function '" << fun
                  << "' in goto-program; not enforcing contracts."
                  << messaget::eom;
      continue;
    }

    if(!fail)
      fail |= enforce_contract(fun);
  }
  return fail;
}
