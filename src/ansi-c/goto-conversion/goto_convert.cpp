/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert.h"
#include "goto_convert_class.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_builder.h>

#include <goto-programs/remove_skip.h>

#include "destructor.h"

static bool is_empty(const goto_programt &goto_program)
{
  forall_goto_program_instructions(it, goto_program)
    if(!is_skip(goto_program, it))
      return false;

  return true;
}

/// Populate the CATCH instructions with the targets  corresponding to their
/// associated labels
static void finish_catch_push_targets(goto_programt &dest)
{
  std::map<irep_idt, goto_programt::targett> label_targets;

  // in the first pass collect the labels and the corresponding targets
  Forall_goto_program_instructions(it, dest)
  {
    if(!it->labels.empty())
    {
      for(auto label : it->labels)
        // record the label and the corresponding target
        label_targets.insert(std::make_pair(label, it));
    }
  }

  // in the second pass set the targets
  for(auto &instruction : dest.instructions)
  {
    if(
      instruction.is_catch() &&
      instruction.code().get_statement() == ID_push_catch)
    {
      // Populate `targets` with a GOTO instruction target per
      // exception handler if it isn't already populated.
      // (Java handlers, for example, need this finish step; C++
      //  handlers will already be populated by now)

      if(instruction.targets.empty())
      {
        bool handler_added = true;
        const code_push_catcht::exception_listt &handler_list =
          to_code_push_catch(instruction.code()).exception_list();

        for(const auto &handler : handler_list)
        {
          // some handlers may not have been converted (if there was no
          // exception to be caught); in such a situation we abort
          if(label_targets.find(handler.get_label()) == label_targets.end())
          {
            handler_added = false;
            break;
          }
        }

        if(!handler_added)
          continue;

        for(const auto &handler : handler_list)
          instruction.targets.push_back(label_targets.at(handler.get_label()));
      }
    }
  }
}

struct build_declaration_hops_inputst
{
  irep_idt mode;
  irep_idt label;
  goto_programt::targett goto_instruction;
  goto_programt::targett label_instruction;
  node_indext label_scope_index = 0;
  node_indext end_scope_index = 0;
};

goto_convertt::declaration_hop_instrumentationt
goto_convertt::build_declaration_hops(
  goto_programt &program,
  std::unordered_map<irep_idt, symbolt, irep_id_hash> &label_flags,
  const build_declaration_hops_inputst &inputs)
{
  // In the case of a goto jumping into a scope, the declarations (but not the
  // initialisations) need to be executed. This function prepares a
  // transformation from code that looks like -
  //   {
  //     statement_block_a();
  //     if(...)
  //       goto user_label;
  //     statement_block_b();
  //     int x;
  //     x = 0;
  //     statement_block_c();
  //     int y;
  //     y = 0;
  //     statement_block_d();
  //   user_label:
  //     statement_block_e();
  //   }
  // to code which looks like -
  //   {
  //     __CPROVER_bool __CPROVER_going_to::user_label;
  //     __CPROVER_going_to::user_label = false;
  //     statement_block_a();
  //     if(...)
  //     {
  //       __CPROVER_going_to::user_label = true;
  //       goto scope_x_label;
  //     }
  //     statement_block_b();
  //   scope_x_label:
  //     int x;
  //     if __CPROVER_going_to::user_label goto scope_y_label:
  //     x = 0;
  //     statement_block_c();
  //   scope_y_label:
  //     int y;
  //     if __CPROVER_going_to::user_label goto user_label:
  //     y = 0;
  //     statement_block_d();
  //   user_label:
  //     __CPROVER_going_to::user_label = false;
  //     statement_block_e();
  //   }
  //
  // The actual insertion of instructions needs to be performed by the caller,
  // which needs to use the result of this method.

  PRECONDITION(inputs.label_scope_index != inputs.end_scope_index);

  declaration_hop_instrumentationt instructions_to_add;

  const auto flag = [&]() -> symbolt {
    const auto existing_flag = label_flags.find(inputs.label);
    if(existing_flag != label_flags.end())
      return existing_flag->second;
    source_locationt label_location =
      inputs.label_instruction->source_location();
    label_location.set_hide();
    const symbolt &new_flag = get_fresh_aux_symbol(
      bool_typet{},
      CPROVER_PREFIX "going_to",
      id2string(inputs.label),
      label_location,
      inputs.mode,
      symbol_table);
    label_flags.emplace(inputs.label, new_flag);

    // Create and initialise flag.
    instructions_to_add.emplace_back(
      program.instructions.begin(),
      goto_programt::make_decl(new_flag.symbol_expr(), label_location));
    const auto make_clear_flag = [&]() -> goto_programt::instructiont {
      return goto_programt::make_assignment(
        new_flag.symbol_expr(), false_exprt{}, label_location);
    };
    instructions_to_add.emplace_back(
      program.instructions.begin(), make_clear_flag());

    // Clear flag on arrival at label.
    auto clear_on_arrival = make_clear_flag();
    instructions_to_add.emplace_back(
      inputs.label_instruction, clear_on_arrival);
    return new_flag;
  }();

  auto goto_instruction = inputs.goto_instruction;
  {
    // Set flag before the goto.
    auto goto_location = goto_instruction->source_location();
    goto_location.set_hide();
    auto set_flag = goto_programt::make_assignment(
      flag.symbol_expr(), true_exprt{}, goto_location);
    instructions_to_add.emplace_back(goto_instruction, set_flag);
  }

  auto target = inputs.label_instruction;
  targets.scope_stack.set_current_node(inputs.label_scope_index);
  while(targets.scope_stack.get_current_node() > inputs.end_scope_index)
  {
    node_indext current_node = targets.scope_stack.get_current_node();
    auto &declaration = targets.scope_stack.get_declaration(current_node);
    targets.scope_stack.descend_tree();
    if(!declaration)
      continue;

    bool add_if = declaration->accounted_flags.find(flag.name) ==
                  declaration->accounted_flags.end();
    if(add_if)
    {
      auto declaration_location = declaration->instruction->source_location();
      declaration_location.set_hide();
      auto if_goto = goto_programt::make_goto(
        target, flag.symbol_expr(), declaration_location);
      // this isn't changing any previously existing instruction so we insert
      // directly rather than going through instructions_to_add
      program.instructions.insert(
        std::next(declaration->instruction), std::move(if_goto));
      declaration->accounted_flags.insert(flag.name);
    }
    target = declaration->instruction;
  }

  // Update the goto so that it goes to the first declaration rather than its
  // original/final destination.
  goto_instruction->set_target(target);

  return instructions_to_add;
}

/*******************************************************************	\

Function: goto_convertt::finish_gotos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::finish_gotos(goto_programt &dest, const irep_idt &mode)
{
  std::unordered_map<irep_idt, symbolt, irep_id_hash> label_flags;
  declaration_hop_instrumentationt instructions_to_insert;

  for(const auto &g_it : targets.gotos)
  {
    goto_programt::instructiont &i = *(g_it.first);

    if(i.is_start_thread())
    {
      const irep_idt &goto_label = i.code().get(ID_destination);
      const auto l_it = targets.labels.find(goto_label);

      if(l_it == targets.labels.end())
      {
        throw incorrect_goto_program_exceptiont(
          "goto label \'" + id2string(goto_label) + "\' not found",
          i.code().find_source_location());
      }

      i.targets.push_back(l_it->second.first);
    }
    else if(i.is_incomplete_goto())
    {
      const irep_idt &goto_label = i.code().get(ID_destination);
      const auto l_it = targets.labels.find(goto_label);

      if(l_it == targets.labels.end())
      {
        throw incorrect_goto_program_exceptiont(
          "goto label \'" + id2string(goto_label) + "\' not found",
          i.code().find_source_location());
      }

      i.complete_goto(l_it->second.first);

      node_indext label_target = l_it->second.second;
      node_indext goto_target = g_it.second;

      // Compare the currently-live variables on the path of the GOTO and label.
      // We want to work out what variables should die during the jump.
      ancestry_resultt intersection_result =
        targets.scope_stack.get_nearest_common_ancestor_info(
          goto_target, label_target);

      // If our goto had no variables of note, just skip (0 is the index of the
      // root of the scope tree)
      if(goto_target != 0)
      {
        // If the goto recorded a destructor stack, execute as much as is
        // appropriate for however many automatic variables leave scope.
        debug().source_location = i.source_location();
        debug() << "adding goto-destructor code on jump to '" << goto_label
                << "'" << eom;

        node_indext end_destruct = intersection_result.common_ancestor;
        goto_programt destructor_code;
        unwind_destructor_stack(
          i.source_location(),
          destructor_code,
          mode,
          end_destruct,
          goto_target);
        dest.destructive_insert(g_it.first, destructor_code);

        // This should leave iterators intact, as long as
        // goto_programt::instructionst is std::list.
      }

      // Variables *entering* scope on goto, is illegal for C++ non-pod types
      // and impossible in Java. However, with the exception of Variable Length
      // Arrays (VLAs), this is valid C and should be taken into account.
      const bool variables_added_to_scope =
        intersection_result.right_depth_below_common_ancestor > 0;
      if(variables_added_to_scope)
      {
        // If the goto recorded a destructor stack, execute as much as is
        // appropriate for however many automatic variables leave scope.
        debug().source_location = i.source_location();
        debug() << "encountered goto '" << goto_label
                << "' that enters one or more lexical blocks; "
                << "adding declaration code on jump to '" << goto_label << "'"
                << eom;

        build_declaration_hops_inputst inputs;
        inputs.mode = mode;
        inputs.label = l_it->first;
        inputs.goto_instruction = g_it.first;
        inputs.label_instruction = l_it->second.first;
        inputs.label_scope_index = label_target;
        inputs.end_scope_index = intersection_result.common_ancestor;
        instructions_to_insert.splice(
          instructions_to_insert.end(),
          build_declaration_hops(dest, label_flags, inputs));
      }
    }
    else
    {
      UNREACHABLE;
    }
  }

  for(auto r_it = instructions_to_insert.rbegin();
      r_it != instructions_to_insert.rend();
      ++r_it)
  {
    dest.insert_before_swap(r_it->first, r_it->second);
  }

  targets.gotos.clear();
}

void goto_convertt::finish_computed_gotos(goto_programt &goto_program)
{
  for(auto &g_it : targets.computed_gotos)
  {
    goto_programt::instructiont &i = *g_it;
    dereference_exprt destination = to_dereference_expr(i.code().op0());
    const exprt pointer = destination.pointer();

    // remember the expression for later checks
    i =
      goto_programt::make_other(code_expressiont(pointer), i.source_location());

    // insert huge case-split
    for(const auto &label : targets.labels)
    {
      exprt label_expr(ID_label, empty_typet());
      label_expr.set(ID_identifier, label.first);

      const equal_exprt guard(pointer, address_of_exprt(label_expr));

      goto_program.insert_after(
        g_it,
        goto_programt::make_goto(
          label.second.first, guard, i.source_location()));
    }
  }

  targets.computed_gotos.clear();
}

/// Rewrite "if(x) goto z; goto y; z:" into "if(!x) goto y;"
/// This only works if the "goto y" is not a branch target.
/// \par parameters: Destination goto program
void goto_convertt::optimize_guarded_gotos(goto_programt &dest)
{
  // We cannot use a set of targets, as target iterators
  // cannot be compared at this stage.

  // collect targets: reset marking
  for(auto &i : dest.instructions)
    i.target_number = goto_programt::instructiont::nil_target;

  // mark the goto targets
  unsigned cnt = 0;
  for(auto &i : dest.instructions)
    if(i.is_goto())
      i.get_target()->target_number = (++cnt);

  for(auto it = dest.instructions.begin(); it != dest.instructions.end(); it++)
  {
    if(!it->is_goto())
      continue;

    auto it_goto_y = std::next(it);

    if(
      it_goto_y == dest.instructions.end() || !it_goto_y->is_goto() ||
      !it_goto_y->condition().is_constant() ||
      !to_constant_expr(it_goto_y->condition()).is_true() ||
      it_goto_y->is_target())
    {
      continue;
    }

    auto it_z = std::next(it_goto_y);

    if(it_z == dest.instructions.end())
      continue;

    // cannot compare iterators, so compare target number instead
    if(it->get_target()->target_number == it_z->target_number)
    {
      DATA_INVARIANT(
        it->condition().find(ID_C_spec_assigns).is_nil() &&
          it->condition().find(ID_C_spec_loop_invariant).is_nil() &&
          it->condition().find(ID_C_spec_decreases).is_nil(),
        "no loop invariant expected");
      irept y_assigns = it_goto_y->condition().find(ID_C_spec_assigns);
      irept y_loop_invariant =
        it_goto_y->condition().find(ID_C_spec_loop_invariant);
      irept y_decreases = it_goto_y->condition().find(ID_C_spec_decreases);

      it->set_target(it_goto_y->get_target());
      exprt updated_condition = boolean_negate(it->condition());
      if(y_assigns.is_not_nil())
        updated_condition.add(ID_C_spec_assigns).swap(y_assigns);
      if(y_loop_invariant.is_not_nil())
        updated_condition.add(ID_C_spec_loop_invariant).swap(y_loop_invariant);
      if(y_decreases.is_not_nil())
        updated_condition.add(ID_C_spec_decreases).swap(y_decreases);
      it->condition_nonconst() = updated_condition;
      it_goto_y->turn_into_skip();
    }
  }
}

void goto_convertt::goto_convert(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  goto_convert_rec(code, dest, mode);
}

void goto_convertt::goto_convert_rec(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  convert(code, dest, mode);

  finish_gotos(dest, mode);
  finish_computed_gotos(dest);
  optimize_guarded_gotos(dest);
  finish_catch_push_targets(dest);
}

void goto_convertt::copy(
  const codet &code,
  goto_program_instruction_typet type,
  goto_programt &dest)
{
  dest.add(goto_programt::instructiont(
    code, code.source_location(), type, nil_exprt(), {}));
}

void goto_convertt::convert_label(
  const code_labelt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  // grab the label
  const irep_idt &label = code.get_label();

  goto_programt tmp;

  // magic thread creation label.
  // The "__CPROVER_ASYNC_" signals the start of a sequence of instructions
  // that can be executed in parallel, i.e, a new thread.
  if(label.starts_with(CPROVER_PREFIX "ASYNC_"))
  {
    // the body of the thread is expected to be
    // in the operand.
    DATA_INVARIANT(
      to_code_label(code).code().is_not_nil(),
      "code() in magic thread creation label is null");

    // replace the magic thread creation label with a
    // thread block (START_THREAD...END_THREAD).
    code_blockt thread_body;
    thread_body.add(to_code_label(code).code());
    thread_body.add_source_location() = code.source_location();
    generate_thread_block(thread_body, dest, mode);
  }
  else
  {
    convert(to_code_label(code).code(), tmp, mode);

    goto_programt::targett target = tmp.instructions.begin();
    dest.destructive_append(tmp);

    targets.labels.insert(
      {label, {target, targets.scope_stack.get_current_node()}});
    target->labels.push_front(label);
  }
}

void goto_convertt::convert_gcc_local_label(const codet &, goto_programt &)
{
  // ignore for now
}

void goto_convertt::convert_switch_case(
  const code_switch_caset &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  goto_programt tmp;
  convert(code.code(), tmp, mode);

  goto_programt::targett target = tmp.instructions.begin();
  dest.destructive_append(tmp);

  // is a default target given?

  if(code.is_default())
    targets.set_default(target);
  else
  {
    // cases?

    cases_mapt::iterator cases_entry = targets.cases_map.find(target);
    if(cases_entry == targets.cases_map.end())
    {
      targets.cases.push_back(std::make_pair(target, caset()));
      cases_entry =
        targets.cases_map.insert(std::make_pair(target, --targets.cases.end()))
          .first;
    }

    exprt::operandst &case_op_dest = cases_entry->second->second;
    case_op_dest.push_back(code.case_op());
    // make sure we have a source location in the case operand as otherwise we
    // end up with a GOTO instruction without a source location
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      case_op_dest.back().source_location().is_not_nil(),
      "case operand should have a source location",
      case_op_dest.back().pretty(),
      code.pretty());
  }
}

void goto_convertt::convert_gcc_switch_case_range(
  const code_gcc_switch_case_ranget &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const auto lb = numeric_cast<mp_integer>(code.lower());
  const auto ub = numeric_cast<mp_integer>(code.upper());

  INVARIANT_WITH_DIAGNOSTICS(
    lb.has_value() && ub.has_value(),
    "GCC's switch-case-range statement requires constant bounds",
    code.find_source_location());

  if(*lb > *ub)
  {
    warning().source_location = code.find_source_location();
    warning() << "GCC's switch-case-range statement with empty case range"
              << eom;
  }

  goto_programt tmp;
  convert(code.code(), tmp, mode);

  goto_programt::targett target = tmp.instructions.begin();
  dest.destructive_append(tmp);

  cases_mapt::iterator cases_entry = targets.cases_map.find(target);
  if(cases_entry == targets.cases_map.end())
  {
    targets.cases.push_back({target, caset()});
    cases_entry =
      targets.cases_map.insert({target, --targets.cases.end()}).first;
  }

  // create a skeleton for case_guard
  cases_entry->second->second.push_back(and_exprt{
    binary_relation_exprt{code.lower(), ID_le, nil_exprt{}},
    binary_relation_exprt{nil_exprt{}, ID_le, code.upper()}});
}

/// converts 'code' and appends the result to 'dest'
void goto_convertt::convert(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const irep_idt &statement = code.get_statement();

  if(statement == ID_block)
    convert_block(to_code_block(code), dest, mode);
  else if(statement == ID_decl)
    convert_frontend_decl(to_code_frontend_decl(code), dest, mode);
  else if(statement == ID_decl_type)
    convert_decl_type(code, dest);
  else if(statement == ID_expression)
    convert_expression(to_code_expression(code), dest, mode);
  else if(statement == ID_assign)
    convert_assign(to_code_assign(code), dest, mode);
  else if(statement == ID_assert)
    convert_assert(to_code_assert(code), dest, mode);
  else if(statement == ID_assume)
    convert_assume(to_code_assume(code), dest, mode);
  else if(statement == ID_function_call)
    convert_function_call(to_code_function_call(code), dest, mode);
  else if(statement == ID_label)
    convert_label(to_code_label(code), dest, mode);
  else if(statement == ID_gcc_local_label)
    convert_gcc_local_label(code, dest);
  else if(statement == ID_switch_case)
    convert_switch_case(to_code_switch_case(code), dest, mode);
  else if(statement == ID_gcc_switch_case_range)
    convert_gcc_switch_case_range(
      to_code_gcc_switch_case_range(code), dest, mode);
  else if(statement == ID_for)
    convert_for(to_code_for(code), dest, mode);
  else if(statement == ID_while)
    convert_while(to_code_while(code), dest, mode);
  else if(statement == ID_dowhile)
    convert_dowhile(to_code_dowhile(code), dest, mode);
  else if(statement == ID_switch)
    convert_switch(to_code_switch(code), dest, mode);
  else if(statement == ID_break)
    convert_break(to_code_break(code), dest, mode);
  else if(statement == ID_return)
    convert_return(to_code_frontend_return(code), dest, mode);
  else if(statement == ID_continue)
    convert_continue(to_code_continue(code), dest, mode);
  else if(statement == ID_goto)
    convert_goto(to_code_goto(code), dest);
  else if(statement == ID_gcc_computed_goto)
    convert_gcc_computed_goto(code, dest);
  else if(statement == ID_skip)
    convert_skip(code, dest);
  else if(statement == ID_ifthenelse)
    convert_ifthenelse(to_code_ifthenelse(code), dest, mode);
  else if(statement == ID_start_thread)
    convert_start_thread(code, dest);
  else if(statement == ID_end_thread)
    convert_end_thread(code, dest);
  else if(statement == ID_atomic_begin)
    convert_atomic_begin(code, dest);
  else if(statement == ID_atomic_end)
    convert_atomic_end(code, dest);
  else if(statement == ID_cpp_delete || statement == "cpp_delete[]")
    convert_cpp_delete(code, dest);
  else if(statement == ID_msc_try_except)
    convert_msc_try_except(code, dest, mode);
  else if(statement == ID_msc_try_finally)
    convert_msc_try_finally(code, dest, mode);
  else if(statement == ID_msc_leave)
    convert_msc_leave(code, dest, mode);
  else if(statement == ID_try_catch) // C++ try/catch
    convert_try_catch(code, dest, mode);
  else if(statement == ID_CPROVER_try_catch) // CPROVER-homemade
    convert_CPROVER_try_catch(code, dest, mode);
  else if(statement == ID_CPROVER_throw) // CPROVER-homemade
    convert_CPROVER_throw(code, dest, mode);
  else if(statement == ID_CPROVER_try_finally)
    convert_CPROVER_try_finally(code, dest, mode);
  else if(statement == ID_asm)
    convert_asm(to_code_asm(code), dest);
  else if(statement == ID_static_assert)
  {
    PRECONDITION(code.operands().size() == 2);
    exprt assertion =
      typecast_exprt::conditional_cast(code.op0(), bool_typet());
    simplify(assertion, ns);
    INVARIANT_WITH_DIAGNOSTICS(
      !assertion.is_constant() || !to_constant_expr(assertion).is_false(),
      "static assertion " + id2string(get_string_constant(code.op1())),
      code.op0().find_source_location());
  }
  else if(statement == ID_dead)
    copy(code, DEAD, dest);
  else if(statement == ID_decl_block)
  {
    for(const auto &op : code.operands())
      convert(to_code(op), dest, mode);
  }
  else if(
    statement == ID_push_catch || statement == ID_pop_catch ||
    statement == ID_exception_landingpad)
    copy(code, CATCH, dest);
  else
    copy(code, OTHER, dest);

  // make sure dest is never empty
  if(dest.instructions.empty())
  {
    dest.add(goto_programt::make_skip(code.source_location()));
  }
}

void goto_convertt::convert_block(
  const code_blockt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const source_locationt &end_location = code.end_location();

  // this saves the index of the destructor stack
  node_indext old_stack_top = targets.scope_stack.get_current_node();

  // now convert block
  for(const auto &b_code : code.statements())
    convert(b_code, dest, mode);

  // see if we need to do any destructors -- may have been processed
  // in a prior break/continue/return already, don't create dead code
  if(
    !dest.empty() && dest.instructions.back().is_goto() &&
    dest.instructions.back().condition().is_constant() &&
    to_constant_expr(dest.instructions.back().condition()).is_true())
  {
    // don't do destructors when we are unreachable
  }
  else
    unwind_destructor_stack(end_location, dest, mode, old_stack_top);

  // Set the current node of our destructor stack back to before the block.
  targets.scope_stack.set_current_node(old_stack_top);
}

void goto_convertt::convert_expression(
  const code_expressiont &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt expr = code.expression();

  if(expr.id() == ID_if)
  {
    // We do a special treatment for c?t:f
    // by compiling to if(c) t; else f;
    const if_exprt &if_expr = to_if_expr(expr);
    code_ifthenelset tmp_code(
      if_expr.cond(),
      code_expressiont(if_expr.true_case()),
      code_expressiont(if_expr.false_case()));
    tmp_code.add_source_location() = expr.source_location();
    tmp_code.then_case().add_source_location() = expr.source_location();
    tmp_code.else_case().add_source_location() = expr.source_location();
    convert_ifthenelse(tmp_code, dest, mode);
  }
  else
  {
    // result _not_ used
    clean_expr_resultt side_effects = clean_expr(expr, mode, false);
    dest.destructive_append(side_effects.side_effects);

    // Any residual expression?
    // We keep it to add checks later.
    if(expr.is_not_nil())
    {
      codet tmp = code;
      tmp.op0() = expr;
      tmp.add_source_location() = expr.source_location();
      copy(tmp, OTHER, dest);
    }

    destruct_locals(side_effects.temporaries, dest, ns);
  }
}

void goto_convertt::convert_frontend_decl(
  const code_frontend_declt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const irep_idt &identifier = code.get_identifier();

  const symbolt &symbol = ns.lookup(identifier);

  if(symbol.is_static_lifetime || symbol.type.id() == ID_code)
    return; // this is a SKIP!

  const goto_programt::targett declaration_iterator = [&]() {
    if(code.operands().size() == 1)
    {
      copy(code, DECL, dest);
      return std::prev(dest.instructions.end());
    }

    exprt initializer = code.op1();

    codet tmp = code;
    tmp.operands().resize(1);
    // hide this declaration-without-initializer step in the goto trace
    tmp.add_source_location().set_hide();

    // Break up into decl and assignment.
    // Decl must be visible before initializer.
    copy(tmp, DECL, dest);
    const auto declaration_iterator = std::prev(dest.instructions.end());

    auto initializer_location = initializer.find_source_location();
    clean_expr_resultt side_effects = clean_expr(initializer, mode);
    dest.destructive_append(side_effects.side_effects);

    if(initializer.is_not_nil())
    {
      code_assignt assign(code.op0(), initializer);
      assign.add_source_location() = initializer_location;

      convert_assign(assign, dest, mode);
    }

    destruct_locals(side_effects.temporaries, dest, ns);

    return declaration_iterator;
  }();

  // now create a 'dead' instruction -- will be added after the
  // destructor created below as unwind_destructor_stack pops off the
  // top of the destructor stack
  const symbol_exprt symbol_expr(symbol.name, symbol.type);

  {
    code_deadt code_dead(symbol_expr);

    targets.scope_stack.add(code_dead, {declaration_iterator});
  }

  // do destructor
  code_function_callt destructor = get_destructor(ns, symbol.type);

  if(destructor.is_not_nil())
  {
    // add "this"
    address_of_exprt this_expr(symbol_expr, pointer_type(symbol.type));
    destructor.arguments().push_back(this_expr);

    targets.scope_stack.add(destructor, {});
  }
}

void goto_convertt::convert_decl_type(const codet &, goto_programt &)
{
  // we remove these
}

void goto_convertt::convert_assign(
  const code_assignt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt lhs = code.lhs(), rhs = code.rhs();

  clean_expr_resultt side_effects = clean_expr(lhs, mode);
  dest.destructive_append(side_effects.side_effects);

  if(rhs.id() == ID_side_effect && rhs.get(ID_statement) == ID_function_call)
  {
    const auto &rhs_function_call = to_side_effect_expr_function_call(rhs);

    INVARIANT_WITH_DIAGNOSTICS(
      rhs.operands().size() == 2,
      "function_call sideeffect takes two operands",
      rhs.find_source_location());

    Forall_operands(it, rhs)
    {
      side_effects.add(clean_expr(*it, mode));
      dest.destructive_append(side_effects.side_effects);
    }

    do_function_call(
      lhs,
      rhs_function_call.function(),
      rhs_function_call.arguments(),
      dest,
      mode);
  }
  else if(
    rhs.id() == ID_side_effect && (rhs.get(ID_statement) == ID_cpp_new ||
                                   rhs.get(ID_statement) == ID_cpp_new_array))
  {
    Forall_operands(it, rhs)
    {
      side_effects.add(clean_expr(*it, mode));
      dest.destructive_append(side_effects.side_effects);
    }

    // TODO: This should be done in a separate pass
    do_cpp_new(lhs, to_side_effect_expr(rhs), dest);
  }
  else if(
    rhs.id() == ID_side_effect &&
    (rhs.get(ID_statement) == ID_assign ||
     rhs.get(ID_statement) == ID_postincrement ||
     rhs.get(ID_statement) == ID_preincrement ||
     rhs.get(ID_statement) == ID_statement_expression ||
     rhs.get(ID_statement) == ID_gcc_conditional_expression))
  {
    // handle above side effects
    side_effects.add(clean_expr(rhs, mode));
    dest.destructive_append(side_effects.side_effects);

    code_assignt new_assign(code);
    new_assign.lhs() = lhs;
    new_assign.rhs() = rhs;

    copy(new_assign, ASSIGN, dest);
  }
  else if(rhs.id() == ID_side_effect)
  {
    // preserve side effects that will be handled at later stages,
    // such as allocate, new operators of other languages, e.g. java, etc
    Forall_operands(it, rhs)
    {
      side_effects.add(clean_expr(*it, mode));
      dest.destructive_append(side_effects.side_effects);
    }

    code_assignt new_assign(code);
    new_assign.lhs() = lhs;
    new_assign.rhs() = rhs;

    copy(new_assign, ASSIGN, dest);
  }
  else
  {
    // do everything else
    side_effects.add(clean_expr(rhs, mode));
    dest.destructive_append(side_effects.side_effects);

    code_assignt new_assign(code);
    new_assign.lhs() = lhs;
    new_assign.rhs() = rhs;

    copy(new_assign, ASSIGN, dest);
  }

  destruct_locals(side_effects.temporaries, dest, ns);
}

void goto_convertt::convert_cpp_delete(const codet &code, goto_programt &dest)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 1,
    "cpp_delete statement takes one operand",
    code.find_source_location());

  exprt tmp_op = code.op0();

  clean_expr_resultt side_effects = clean_expr(tmp_op, ID_cpp);
  dest.destructive_append(side_effects.side_effects);

  // we call the destructor, and then free
  const exprt &destructor =
    static_cast<const exprt &>(code.find(ID_destructor));

  irep_idt delete_identifier;

  if(code.get_statement() == ID_cpp_delete_array)
    delete_identifier = "__delete_array";
  else if(code.get_statement() == ID_cpp_delete)
    delete_identifier = "__delete";
  else
    UNREACHABLE;

  if(destructor.is_not_nil())
  {
    if(code.get_statement() == ID_cpp_delete_array)
    {
      // build loop
    }
    else if(code.get_statement() == ID_cpp_delete)
    {
      // just one object
      const dereference_exprt deref_op(tmp_op);

      codet tmp_code = to_code(destructor);
      replace_new_object(deref_op, tmp_code);
      convert(tmp_code, dest, ID_cpp);
    }
    else
      UNREACHABLE;
  }

  // now do "free"
  exprt delete_symbol = ns.lookup(delete_identifier).symbol_expr();

  DATA_INVARIANT(
    to_code_type(delete_symbol.type()).parameters().size() == 1,
    "delete statement takes 1 parameter");

  typet arg_type =
    to_code_type(delete_symbol.type()).parameters().front().type();

  code_function_callt delete_call(
    delete_symbol, {typecast_exprt(tmp_op, arg_type)});
  delete_call.add_source_location() = code.source_location();

  convert(delete_call, dest, ID_cpp);

  destruct_locals(side_effects.temporaries, dest, ns);
}

void goto_convertt::convert_assert(
  const code_assertt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt cond = code.assertion();

  clean_expr_resultt side_effects = clean_expr(cond, mode);
  dest.destructive_append(side_effects.side_effects);

  source_locationt annotated_location = code.source_location();
  annotated_location.set("user-provided", true);
  dest.add(goto_programt::make_assertion(cond, annotated_location));

  destruct_locals(side_effects.temporaries, dest, ns);
}

void goto_convertt::convert_skip(const codet &code, goto_programt &dest)
{
  dest.add(goto_programt::instructiont(
    code, code.source_location(), SKIP, nil_exprt(), {}));
}

void goto_convertt::convert_assume(
  const code_assumet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt op = code.assumption();

  clean_expr_resultt side_effects = clean_expr(op, mode);
  dest.destructive_append(side_effects.side_effects);

  dest.add(goto_programt::make_assumption(op, code.source_location()));

  destruct_locals(side_effects.temporaries, dest, ns);
}

void goto_convertt::convert_loop_contracts(
  const codet &code,
  goto_programt::targett loop)
{
  auto assigns = static_cast<const unary_exprt &>(code.find(ID_C_spec_assigns));
  if(assigns.is_not_nil())
  {
    PRECONDITION(loop->is_goto() || loop->is_incomplete_goto());
    loop->condition_nonconst().add(ID_C_spec_assigns).swap(assigns.op());
  }

  auto invariant =
    static_cast<const exprt &>(code.find(ID_C_spec_loop_invariant));
  if(!invariant.is_nil())
  {
    PRECONDITION(loop->is_goto() || loop->is_incomplete_goto());
    loop->condition_nonconst().add(ID_C_spec_loop_invariant).swap(invariant);
  }

  auto decreases_clause =
    static_cast<const exprt &>(code.find(ID_C_spec_decreases));
  if(!decreases_clause.is_nil())
  {
    PRECONDITION(loop->is_goto() || loop->is_incomplete_goto());
    loop->condition_nonconst().add(ID_C_spec_decreases).swap(decreases_clause);
  }
}

void goto_convertt::convert_for(
  const code_fort &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  // turn for(A; c; B) { P } into
  //  A; while(c) { P; B; }
  //-----------------------------
  //    A;
  // u: sideeffects in c
  // v: if(!c) goto Z;
  //    cleanup-loop;
  // w: P;
  // x: B;               <-- continue target
  // y: goto u;
  // Z: cleanup-out;
  // z: ;                <-- break target

  // A;
  if(code.init().is_not_nil())
    convert(to_code(code.init()), dest, mode);

  exprt cond = code.cond();

  clean_expr_resultt side_effects = clean_expr(cond, mode);

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the u label
  goto_programt::targett u = side_effects.side_effects.instructions.begin();

  // do the v label
  goto_programt tmp_v;
  goto_programt::targett v = tmp_v.add(goto_programt::instructiont());
  destruct_locals(side_effects.temporaries, tmp_v, ns);

  // do the z and Z labels
  goto_programt tmp_z;
  destruct_locals(side_effects.temporaries, tmp_z, ns);
  goto_programt::targett z =
    tmp_z.add(goto_programt::make_skip(code.source_location()));
  goto_programt::targett Z = tmp_z.instructions.begin();

  // do the x label
  goto_programt tmp_x;

  if(code.iter().is_nil())
  {
    tmp_x.add(goto_programt::make_skip(code.source_location()));
  }
  else
  {
    exprt tmp_B = code.iter();

    clean_expr_resultt side_effects_iter = clean_expr(tmp_B, mode, false);
    tmp_x.destructive_append(side_effects_iter.side_effects);
    destruct_locals(side_effects_iter.temporaries, tmp_x, ns);

    if(tmp_x.instructions.empty())
      tmp_x.add(goto_programt::make_skip(code.source_location()));
  }

  // optimize the v label
  if(side_effects.side_effects.instructions.empty())
    u = v;

  // set the targets
  targets.set_break(z);
  targets.set_continue(tmp_x.instructions.begin());

  // v: if(!c) goto Z;
  *v =
    goto_programt::make_goto(Z, boolean_negate(cond), cond.source_location());

  // do the w label
  goto_programt tmp_w;
  convert(code.body(), tmp_w, mode);

  // y: goto u;
  goto_programt tmp_y;
  goto_programt::targett y = tmp_y.add(
    goto_programt::make_goto(u, true_exprt(), code.source_location()));

  // assigns clause, loop invariant and decreases clause
  convert_loop_contracts(code, y);

  dest.destructive_append(side_effects.side_effects);
  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue
  old_targets.restore(targets);
}

void goto_convertt::convert_while(
  const code_whilet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const exprt &cond = code.cond();
  const source_locationt &source_location = code.source_location();

  //    while(c) P;
  //--------------------
  // v: sideeffects in c
  //    if(!c) goto z;
  // x: P;
  // y: goto v;          <-- continue target
  // z: ;                <-- break target

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z =
    tmp_z.add(goto_programt::make_skip(source_location));

  goto_programt tmp_branch;
  generate_conditional_branch(
    boolean_negate(cond), z, source_location, tmp_branch, mode);

  // do the v label
  goto_programt::targett v = tmp_branch.instructions.begin();

  // y: goto v;
  goto_programt tmp_y;
  goto_programt::targett y = tmp_y.add(
    goto_programt::make_goto(v, true_exprt(), code.source_location()));

  // set the targets
  targets.set_break(z);
  targets.set_continue(y);

  // do the x label
  goto_programt tmp_x;
  convert(code.body(), tmp_x, mode);

  // assigns clause, loop invariant and decreases clause
  convert_loop_contracts(code, y);

  dest.destructive_append(tmp_branch);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue
  old_targets.restore(targets);
}

void goto_convertt::convert_dowhile(
  const code_dowhilet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 2,
    "dowhile takes two operands",
    code.find_source_location());

  // save source location
  source_locationt condition_location = code.cond().find_source_location();

  exprt cond = code.cond();

  clean_expr_resultt side_effects = clean_expr(cond, mode);

  //    do P while(c);
  //--------------------
  // w: P;
  // x: sideeffects in c   <-- continue target
  // y: if(!c) goto C;
  //    cleanup-loop;
  // W: goto w;
  // C: cleanup-out;
  // z: ;                  <-- break target

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the y label
  goto_programt tmp_y;
  goto_programt::targett y = tmp_y.add(goto_programt::make_incomplete_goto(
    boolean_negate(cond), condition_location));
  destruct_locals(side_effects.temporaries, tmp_y, ns);
  goto_programt::targett W = tmp_y.add(
    goto_programt::make_incomplete_goto(true_exprt{}, condition_location));

  // do the z label and C labels
  goto_programt tmp_z;
  destruct_locals(side_effects.temporaries, tmp_z, ns);
  goto_programt::targett z =
    tmp_z.add(goto_programt::make_skip(code.source_location()));
  goto_programt::targett C = tmp_z.instructions.begin();

  // y: if(!c) goto C;
  y->complete_goto(C);

  // do the x label
  goto_programt::targett x;
  if(side_effects.side_effects.instructions.empty())
    x = y;
  else
    x = side_effects.side_effects.instructions.begin();

  // set the targets
  targets.set_break(z);
  targets.set_continue(x);

  // do the w label
  goto_programt tmp_w;
  convert(code.body(), tmp_w, mode);
  goto_programt::targett w = tmp_w.instructions.begin();

  // W: goto w;
  W->complete_goto(w);

  // assigns_clause, loop invariant and decreases clause
  convert_loop_contracts(code, W);

  dest.destructive_append(tmp_w);
  dest.destructive_append(side_effects.side_effects);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);

  // restore break/continue targets
  old_targets.restore(targets);
}

exprt goto_convertt::case_guard(
  const exprt &value,
  const exprt::operandst &case_op)
{
  PRECONDITION(!case_op.empty());

  exprt::operandst disjuncts;
  disjuncts.reserve(case_op.size());

  for(const auto &op : case_op)
  {
    // could be a skeleton generated by convert_gcc_switch_case_range
    if(op.id() == ID_and)
    {
      const binary_exprt &and_expr = to_binary_expr(op);
      PRECONDITION(to_binary_expr(and_expr.op0()).op1().is_nil());
      PRECONDITION(to_binary_expr(and_expr.op1()).op0().is_nil());
      binary_exprt skeleton = and_expr;
      to_binary_expr(skeleton.op0()).op1() = value;
      to_binary_expr(skeleton.op1()).op0() = value;
      disjuncts.push_back(skeleton);
    }
    else
      disjuncts.push_back(equal_exprt(value, op));
  }

  return disjunction(disjuncts);
}

void goto_convertt::convert_switch(
  const code_switcht &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  // switch(v) {
  //   case x: Px;
  //   case y: Py;
  //   ...
  //   default: Pd;
  // }
  // --------------------
  // location
  // x: if(v==x) goto X;
  // y: if(v==y) goto Y;
  //    goto d;
  // X: Px;
  // Y: Py;
  // d: Pd;
  // z: ;

  // we first add a 'location' node for the switch statement,
  // which would otherwise not be recorded
  dest.add(goto_programt::make_location(code.source_location()));

  // get the location of the end of the body, but
  // default to location of switch, if none
  source_locationt body_end_location =
    code.body().get_statement() == ID_block
      ? to_code_block(code.body()).end_location()
      : code.source_location();

  // do the value we switch over
  exprt argument = code.value();

  clean_expr_resultt side_effects = clean_expr(argument, mode);

  // Avoid potential performance penalties caused by evaluating the value
  // multiple times (as the below chain-of-ifs does). "needs_cleaning" isn't
  // necessarily the right check here, and we may need to introduce a different
  // way of identifying the class of non-trivial expressions that warrant
  // introduction of a temporary.
  if(needs_cleaning(argument))
  {
    symbolt &new_symbol = new_tmp_symbol(
      argument.type(),
      "switch_value",
      side_effects.side_effects,
      code.source_location(),
      mode);

    code_assignt copy_value{
      new_symbol.symbol_expr(), argument, code.source_location()};
    convert(copy_value, side_effects.side_effects, mode);

    argument = new_symbol.symbol_expr();
    side_effects.add_temporary(to_symbol_expr(argument).get_identifier());
  }

  // save break/default/cases targets
  break_switch_targetst old_targets(targets);

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z =
    tmp_z.add(goto_programt::make_skip(body_end_location));

  // set the new targets -- continue stays as is
  targets.set_break(z);
  targets.set_default(z);
  targets.cases.clear();
  targets.cases_map.clear();

  goto_programt tmp;
  convert(code.body(), tmp, mode);

  goto_programt tmp_cases;

  // The case number represents which case this corresponds to in the sequence
  // of case statements.
  //
  // switch (x)
  // {
  // case 2:  // case_number 1
  //   ...;
  // case 3:  // case_number 2
  //   ...;
  // case 10: // case_number 3
  //   ...;
  // }
  size_t case_number = 1;
  for(auto &case_pair : targets.cases)
  {
    const caset &case_ops = case_pair.second;

    if(case_ops.empty())
      continue;

    exprt guard_expr = case_guard(argument, case_ops);

    source_locationt source_location = case_ops.front().find_source_location();
    source_location.set_case_number(std::to_string(case_number));
    case_number++;

    if(side_effects.temporaries.empty())
    {
      guard_expr.add_source_location() = source_location;

      tmp_cases.add(goto_programt::make_goto(
        case_pair.first, std::move(guard_expr), source_location));
    }
    else
    {
      guard_expr = boolean_negate(guard_expr);
      guard_expr.add_source_location() = source_location;

      goto_programt::targett try_next =
        tmp_cases.add(goto_programt::make_incomplete_goto(
          std::move(guard_expr), source_location));
      destruct_locals(side_effects.temporaries, tmp_cases, ns);
      tmp_cases.add(goto_programt::make_goto(
        case_pair.first, true_exprt{}, source_location));
      goto_programt::targett next_case =
        tmp_cases.add(goto_programt::make_skip(source_location));
      try_next->complete_goto(next_case);
    }
  }

  tmp_cases.add(goto_programt::make_goto(
    targets.default_target, targets.default_target->source_location()));

  dest.destructive_append(side_effects.side_effects);
  dest.destructive_append(tmp_cases);
  dest.destructive_append(tmp);
  dest.destructive_append(tmp_z);

  // restore old targets
  old_targets.restore(targets);
}

void goto_convertt::convert_break(
  const code_breakt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    targets.break_set, "break without target", code.find_source_location());

  // need to process destructor stack
  unwind_destructor_stack(
    code.source_location(), dest, mode, targets.break_stack_node);

  // add goto
  dest.add(
    goto_programt::make_goto(targets.break_target, code.source_location()));
}

void goto_convertt::convert_return(
  const code_frontend_returnt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(!targets.return_set)
  {
    throw incorrect_goto_program_exceptiont(
      "return without target", code.find_source_location());
  }

  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().empty() || code.operands().size() == 1,
    "return takes none or one operand",
    code.find_source_location());

  code_frontend_returnt new_code(code);
  clean_expr_resultt side_effects;

  if(new_code.has_return_value())
  {
    bool result_is_used = new_code.return_value().type().id() != ID_empty;

    side_effects = clean_expr(new_code.return_value(), mode, result_is_used);
    dest.destructive_append(side_effects.side_effects);

    // remove void-typed return value
    if(!result_is_used)
      new_code.return_value().make_nil();
  }

  if(targets.has_return_value)
  {
    INVARIANT_WITH_DIAGNOSTICS(
      new_code.has_return_value(),
      "function must return value",
      new_code.find_source_location());

    // Now add a 'set return value' instruction to set the return value.
    dest.add(goto_programt::make_set_return_value(
      new_code.return_value(), new_code.source_location()));
    destruct_locals(side_effects.temporaries, dest, ns);
  }
  else
  {
    INVARIANT_WITH_DIAGNOSTICS(
      !new_code.has_return_value() ||
        new_code.return_value().type().id() == ID_empty,
      "function must not return value",
      code.find_source_location());
  }

  // Need to process _entire_ destructor stack.
  unwind_destructor_stack(code.source_location(), dest, mode);

  // add goto to end-of-function
  dest.add(goto_programt::make_goto(
    targets.return_target, new_code.source_location()));
}

void goto_convertt::convert_continue(
  const code_continuet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    targets.continue_set,
    "continue without target",
    code.find_source_location());

  // need to process destructor stack
  unwind_destructor_stack(
    code.source_location(), dest, mode, targets.continue_stack_node);

  // add goto
  dest.add(
    goto_programt::make_goto(targets.continue_target, code.source_location()));
}

void goto_convertt::convert_goto(const code_gotot &code, goto_programt &dest)
{
  // this instruction will be completed during post-processing
  goto_programt::targett t =
    dest.add(goto_programt::make_incomplete_goto(code, code.source_location()));

  // Loop contracts annotated in GOTO
  convert_loop_contracts(code, t);

  // remember it to do the target later
  targets.gotos.emplace_back(t, targets.scope_stack.get_current_node());
}

void goto_convertt::convert_gcc_computed_goto(
  const codet &code,
  goto_programt &dest)
{
  // this instruction will turn into OTHER during post-processing
  goto_programt::targett t = dest.add(goto_programt::instructiont(
    code, code.source_location(), NO_INSTRUCTION_TYPE, nil_exprt(), {}));

  // remember it to do this later
  targets.computed_gotos.push_back(t);
}

void goto_convertt::convert_start_thread(const codet &code, goto_programt &dest)
{
  goto_programt::targett start_thread = dest.add(goto_programt::instructiont(
    code, code.source_location(), START_THREAD, nil_exprt(), {}));

  // remember it to do target later
  targets.gotos.emplace_back(
    start_thread, targets.scope_stack.get_current_node());
}

void goto_convertt::convert_end_thread(const codet &code, goto_programt &dest)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().empty(),
    "end_thread expects no operands",
    code.find_source_location());

  copy(code, END_THREAD, dest);
}

void goto_convertt::convert_atomic_begin(const codet &code, goto_programt &dest)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().empty(),
    "atomic_begin expects no operands",
    code.find_source_location());

  copy(code, ATOMIC_BEGIN, dest);
}

void goto_convertt::convert_atomic_end(const codet &code, goto_programt &dest)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().empty(),
    ": atomic_end expects no operands",
    code.find_source_location());

  copy(code, ATOMIC_END, dest);
}

void goto_convertt::convert_ifthenelse(
  const code_ifthenelset &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  DATA_INVARIANT(code.then_case().is_not_nil(), "cannot accept an empty body");

  bool has_else = !code.else_case().is_nil();

  const source_locationt &source_location = code.source_location();

  // We do a bit of special treatment for && in the condition
  // in case cleaning would be needed otherwise.
  if(
    code.cond().id() == ID_and && code.cond().operands().size() == 2 &&
    (needs_cleaning(to_binary_expr(code.cond()).op0()) ||
     needs_cleaning(to_binary_expr(code.cond()).op1())) &&
    !has_else)
  {
    // if(a && b) XX --> if(a) if(b) XX
    code_ifthenelset new_if1(
      to_binary_expr(code.cond()).op1(), code.then_case());
    new_if1.add_source_location() = source_location;
    code_ifthenelset new_if0(
      to_binary_expr(code.cond()).op0(), std::move(new_if1));
    new_if0.add_source_location() = source_location;
    return convert_ifthenelse(new_if0, dest, mode);
  }

  exprt tmp_guard = code.cond();
  clean_expr_resultt side_effects = clean_expr(tmp_guard, mode);
  dest.destructive_append(side_effects.side_effects);

  // convert 'then'-branch
  goto_programt tmp_then;
  destruct_locals(side_effects.temporaries, tmp_then, ns);
  convert(code.then_case(), tmp_then, mode);
  source_locationt then_end_location =
    code.then_case().get_statement() == ID_block
      ? to_code_block(code.then_case()).end_location()
      : code.then_case().source_location();

  goto_programt tmp_else;
  destruct_locals(side_effects.temporaries, tmp_else, ns);
  source_locationt else_end_location;

  if(has_else)
  {
    convert(code.else_case(), tmp_else, mode);
    else_end_location = code.else_case().get_statement() == ID_block
                          ? to_code_block(code.else_case()).end_location()
                          : code.else_case().source_location();
  }

  generate_ifthenelse(
    tmp_guard,
    source_location,
    tmp_then,
    then_end_location,
    tmp_else,
    else_end_location,
    dest,
    mode);
}

void goto_convertt::collect_operands(
  const exprt &expr,
  const irep_idt &id,
  std::list<exprt> &dest)
{
  if(expr.id() != id)
  {
    dest.push_back(expr);
  }
  else
  {
    // left-to-right is important
    for(const auto &op : expr.operands())
      collect_operands(op, id, dest);
  }
}

/// This is (believed to be) faster than using std::list.size
/// \par parameters: Goto program 'g'
/// \return True if 'g' has one instruction
static inline bool is_size_one(const goto_programt &g)
{
  return (!g.instructions.empty()) &&
         ++g.instructions.begin() == g.instructions.end();
}

/// if(guard) true_case; else false_case;
void goto_convertt::generate_ifthenelse(
  const exprt &guard,
  const source_locationt &source_location,
  goto_programt &true_case,
  const source_locationt &then_end_location,
  goto_programt &false_case,
  const source_locationt &else_end_location,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(is_empty(true_case) && is_empty(false_case))
  {
    // hmpf. Useless branch.
    goto_programt tmp_z;
    goto_programt::targett z = tmp_z.add(goto_programt::make_skip());
    dest.add(goto_programt::make_goto(z, guard, source_location));
    dest.destructive_append(tmp_z);
    return;
  }

  // do guarded assertions directly
  if(
    is_size_one(true_case) && true_case.instructions.back().is_assert() &&
    true_case.instructions.back().condition().is_constant() &&
    to_constant_expr(true_case.instructions.back().condition()).is_false() &&
    true_case.instructions.back().labels.empty())
  {
    // The above conjunction deliberately excludes the instance
    // if(some) { label: assert(false); }
    true_case.instructions.back().condition_nonconst() = boolean_negate(guard);
    dest.destructive_append(true_case);
    true_case.instructions.clear();
    if(
      is_empty(false_case) ||
      (is_size_one(false_case) &&
       is_skip(false_case, false_case.instructions.begin())))
      return;
  }

  // similarly, do guarded assertions directly
  if(
    is_size_one(false_case) && false_case.instructions.back().is_assert() &&
    false_case.instructions.back().condition().is_constant() &&
    to_constant_expr(false_case.instructions.back().condition()).is_false() &&
    false_case.instructions.back().labels.empty())
  {
    // The above conjunction deliberately excludes the instance
    // if(some) ... else { label: assert(false); }
    false_case.instructions.back().condition_nonconst() = guard;
    dest.destructive_append(false_case);
    false_case.instructions.clear();
    if(
      is_empty(true_case) ||
      (is_size_one(true_case) &&
       is_skip(true_case, true_case.instructions.begin())))
      return;
  }

  // a special case for C libraries that use
  // (void)((cond) || (assert(0),0))
  if(
    is_empty(false_case) && true_case.instructions.size() == 2 &&
    true_case.instructions.front().is_assert() &&
    simplify_expr(true_case.instructions.front().condition(), ns)
      .is_constant() &&
    to_constant_expr(
      simplify_expr(true_case.instructions.front().condition(), ns))
      .is_false() &&
    true_case.instructions.front().labels.empty() &&
    true_case.instructions.back().is_other() &&
    true_case.instructions.back().get_other().get_statement() ==
      ID_expression &&
    true_case.instructions.back().labels.empty())
  {
    true_case.instructions.front().condition_nonconst() = boolean_negate(guard);
    true_case.instructions.erase(--true_case.instructions.end());
    dest.destructive_append(true_case);
    true_case.instructions.clear();

    return;
  }

  // Flip around if no 'true' case code.
  if(is_empty(true_case))
  {
    return generate_ifthenelse(
      boolean_negate(guard),
      source_location,
      false_case,
      else_end_location,
      true_case,
      then_end_location,
      dest,
      mode);
  }

  bool has_else = !is_empty(false_case);

  //    if(c) P;
  //--------------------
  // v: if(!c) goto z;
  // w: P;
  // z: ;

  //    if(c) P; else Q;
  //--------------------
  // v: if(!c) goto y;
  // w: P;
  // x: goto z;
  // y: Q;
  // z: ;

  // do the x label
  goto_programt tmp_x;
  goto_programt::targett x = tmp_x.add(
    goto_programt::make_incomplete_goto(true_exprt(), then_end_location));

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z = tmp_z.add(
    goto_programt::make_skip(has_else ? else_end_location : then_end_location));

  // y: Q;
  goto_programt tmp_y;
  goto_programt::targett y;
  if(has_else)
  {
    tmp_y.swap(false_case);
    y = tmp_y.instructions.begin();
  }

  // v: if(!c) goto z/y;
  goto_programt tmp_v;
  generate_conditional_branch(
    boolean_negate(guard), has_else ? y : z, source_location, tmp_v, mode);

  // w: P;
  goto_programt tmp_w;
  tmp_w.swap(true_case);

  // x: goto z;
  CHECK_RETURN(!tmp_w.instructions.empty());
  x->complete_goto(z);

  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);

  // When the `then` branch of a balanced `if` condition ends with a `return` or
  // a `goto` statement, it is not necessary to add the `goto z` and `z:` goto
  // elements as they are never used.
  // This helps for example when using `--cover location` as such command are
  // marked unreachable, but are not part of the user-provided code to analyze.
  bool then_branch_returns = dest.instructions.rbegin()->is_goto();

  if(has_else)
  {
    // Don't add the `goto` at the end of the `then` branch if not needed
    if(!then_branch_returns)
    {
      dest.destructive_append(tmp_x);
    }
    dest.destructive_append(tmp_y);
  }

  // Don't add the `z` label at the end of the `if` when not needed.
  if(!has_else || !then_branch_returns)
  {
    dest.destructive_append(tmp_z);
  }
}

/// if(guard) goto target;
static bool has_and_or(const exprt &expr)
{
  for(const auto &op : expr.operands())
  {
    if(has_and_or(op))
      return true;
  }

  if(expr.id() == ID_and || expr.id() == ID_or)
    return true;

  return false;
}

void goto_convertt::generate_conditional_branch(
  const exprt &guard,
  goto_programt::targett target_true,
  const source_locationt &source_location,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(has_and_or(guard) && needs_cleaning(guard))
  {
    // if(guard) goto target;
    //   becomes
    // if(guard) goto target; else goto next;
    // next: skip;

    goto_programt tmp;
    goto_programt::targett target_false =
      tmp.add(goto_programt::make_skip(source_location));

    generate_conditional_branch(
      guard, target_true, target_false, source_location, dest, mode);

    dest.destructive_append(tmp);
  }
  else
  {
    // simple branch
    exprt cond = guard;
    clean_expr_resultt side_effects = clean_expr(cond, mode);
    dest.destructive_append(side_effects.side_effects);

    dest.add(goto_programt::make_goto(target_true, cond, source_location));
    goto_programt tmp_destruct;
    destruct_locals(side_effects.temporaries, tmp_destruct, ns);
    dest.insert_before_swap(target_true, tmp_destruct);
    destruct_locals(side_effects.temporaries, dest, ns);
  }
}

/// if(guard) goto target_true; else goto target_false;
void goto_convertt::generate_conditional_branch(
  const exprt &guard,
  goto_programt::targett target_true,
  goto_programt::targett target_false,
  const source_locationt &source_location,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(guard.id() == ID_not)
  {
    // simply swap targets
    generate_conditional_branch(
      to_not_expr(guard).op(),
      target_false,
      target_true,
      source_location,
      dest,
      mode);
    return;
  }

  if(guard.id() == ID_and)
  {
    // turn
    //   if(a && b) goto target_true; else goto target_false;
    // into
    //    if(!a) goto target_false;
    //    if(!b) goto target_false;
    //    goto target_true;

    std::list<exprt> op;
    collect_operands(guard, guard.id(), op);

    for(const auto &expr : op)
      generate_conditional_branch(
        boolean_negate(expr), target_false, source_location, dest, mode);

    dest.add(goto_programt::make_goto(target_true, source_location));

    return;
  }
  else if(guard.id() == ID_or)
  {
    // turn
    //   if(a || b) goto target_true; else goto target_false;
    // into
    //   if(a) goto target_true;
    //   if(b) goto target_true;
    //   goto target_false;

    std::list<exprt> op;
    collect_operands(guard, guard.id(), op);

    // true branch(es)
    for(const auto &expr : op)
      generate_conditional_branch(
        expr, target_true, source_location, dest, mode);

    // false branch
    dest.add(goto_programt::make_goto(target_false, guard.source_location()));

    return;
  }

  exprt cond = guard;
  clean_expr_resultt side_effects = clean_expr(cond, mode);
  dest.destructive_append(side_effects.side_effects);

  // true branch
  dest.add(goto_programt::make_goto(target_true, cond, source_location));
  goto_programt tmp_destruct;
  destruct_locals(side_effects.temporaries, tmp_destruct, ns);
  dest.insert_before_swap(target_true, tmp_destruct);

  // false branch
  dest.add(goto_programt::make_goto(target_false, source_location));
  destruct_locals(side_effects.temporaries, tmp_destruct, ns);
  dest.insert_before_swap(target_false, tmp_destruct);
}

bool goto_convertt::get_string_constant(const exprt &expr, irep_idt &value)
{
  if(expr.id() == ID_typecast)
    return get_string_constant(to_typecast_expr(expr).op(), value);

  if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_index)
  {
    exprt index_op =
      get_constant(to_index_expr(to_address_of_expr(expr).object()).array());
    simplify(index_op, ns);

    if(index_op.id() == ID_string_constant)
    {
      value = to_string_constant(index_op).value();
      return false;
    }
    else if(index_op.id() == ID_array)
    {
      std::string result;
      for(const auto &op : as_const(index_op).operands())
      {
        if(op.is_constant())
        {
          const auto i = numeric_cast<std::size_t>(op);
          if(!i.has_value())
            return true;

          if(i.value() != 0) // to skip terminating 0
            result += static_cast<char>(i.value());
        }
      }

      return value = result, false;
    }
  }

  if(expr.id() == ID_string_constant)
  {
    value = to_string_constant(expr).value();
    return false;
  }

  return true;
}

irep_idt goto_convertt::get_string_constant(const exprt &expr)
{
  irep_idt result;

  const bool res = get_string_constant(expr, result);
  INVARIANT_WITH_DIAGNOSTICS(
    !res,
    "expected string constant",
    expr.find_source_location(),
    expr.pretty());

  return result;
}

exprt goto_convertt::get_constant(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    const symbolt &symbol = ns.lookup(to_symbol_expr(expr));

    return symbol.value;
  }
  else if(expr.id() == ID_member)
  {
    auto tmp = to_member_expr(expr);
    tmp.compound() = get_constant(tmp.compound());
    return std::move(tmp);
  }
  else if(expr.id() == ID_index)
  {
    auto tmp = to_index_expr(expr);
    tmp.op0() = get_constant(tmp.op0());
    tmp.op1() = get_constant(tmp.op1());
    return std::move(tmp);
  }
  else
    return expr;
}

symbolt &goto_convertt::new_tmp_symbol(
  const typet &type,
  const std::string &suffix,
  goto_programt &dest,
  const source_locationt &source_location,
  const irep_idt &mode)
{
  PRECONDITION(!mode.empty());
  symbolt &new_symbol = get_fresh_aux_symbol(
    type,
    tmp_symbol_prefix,
    "tmp_" + suffix,
    source_location,
    mode,
    symbol_table);

  if(type.id() != ID_code)
  {
    dest.add(
      goto_programt::make_decl(new_symbol.symbol_expr(), source_location));
  }

  return new_symbol;
}

irep_idt goto_convertt::make_temp_symbol(
  exprt &expr,
  const std::string &suffix,
  goto_programt &dest,
  const irep_idt &mode)
{
  const source_locationt source_location = expr.find_source_location();

  symbolt &new_symbol =
    new_tmp_symbol(expr.type(), suffix, dest, source_location, mode);

  code_assignt assignment;
  assignment.lhs() = new_symbol.symbol_expr();
  assignment.rhs() = expr;
  assignment.add_source_location() = source_location;

  convert(assignment, dest, mode);

  expr = new_symbol.symbol_expr();

  return to_symbol_expr(expr).get_identifier();
}

void goto_convert(
  const codet &code,
  symbol_table_baset &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler,
  const irep_idt &mode)
{
  symbol_table_buildert symbol_table_builder =
    symbol_table_buildert::wrap(symbol_table);
  goto_convertt goto_convert(symbol_table_builder, message_handler);
  goto_convert.goto_convert(code, dest, mode);
}

void goto_convert(
  symbol_table_baset &symbol_table,
  goto_programt &dest,
  message_handlert &message_handler)
{
  // find main symbol
  const symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find("main");

  DATA_INVARIANT(
    s_it != symbol_table.symbols.end(), "failed to find main symbol");

  const symbolt &symbol = s_it->second;

  ::goto_convert(
    to_code(symbol.value), symbol_table, dest, message_handler, symbol.mode);
}

/// Generates the necessary goto-instructions to represent a thread-block.
/// Specifically, the following instructions are generated:
///
/// A: START_THREAD : C
/// B: GOTO Z
/// C: SKIP
/// D: {THREAD BODY}
/// E: END_THREAD
/// Z: SKIP
///
/// \param thread_body: Sequence of codet's that can be executed
///   in parallel
/// \param [out] dest: Resulting goto-instructions
/// \param mode: Language mode
void goto_convertt::generate_thread_block(
  const code_blockt &thread_body,
  goto_programt &dest,
  const irep_idt &mode)
{
  goto_programt preamble, body, postamble;

  goto_programt::targett c = body.add(goto_programt::make_skip());
  convert(thread_body, body, mode);

  postamble.add(goto_programt::instructiont(
    static_cast<const codet &>(get_nil_irep()),
    thread_body.source_location(),
    END_THREAD,
    nil_exprt(),
    {}));
  goto_programt::targett z = postamble.add(goto_programt::make_skip());

  preamble.add(goto_programt::instructiont(
    static_cast<const codet &>(get_nil_irep()),
    thread_body.source_location(),
    START_THREAD,
    nil_exprt(),
    {c}));
  preamble.add(goto_programt::make_goto(z, thread_body.source_location()));

  dest.destructive_append(preamble);
  dest.destructive_append(body);
  dest.destructive_append(postamble);
}
