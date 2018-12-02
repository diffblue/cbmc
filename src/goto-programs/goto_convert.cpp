/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/symbol_table_builder.h>

#include "goto_convert_class.h"
#include "destructor.h"
#include "remove_skip.h"

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
  Forall_goto_program_instructions(it, dest)
  {
    if(it->is_catch() && it->code.get_statement()==ID_push_catch)
    {
      // Populate `targets` with a GOTO instruction target per
      // exception handler if it isn't already populated.
      // (Java handlers, for example, need this finish step; C++
      //  handlers will already be populated by now)

      if(it->targets.empty())
      {
        bool handler_added=true;
        const code_push_catcht::exception_listt &handler_list=
          to_code_push_catch(it->code).exception_list();

        for(const auto &handler : handler_list)
        {
          // some handlers may not have been converted (if there was no
          // exception to be caught); in such a situation we abort
          if(label_targets.find(handler.get_label())==label_targets.end())
          {
            handler_added=false;
            break;
          }
        }

        if(!handler_added)
          continue;

        for(const auto &handler : handler_list)
          it->targets.push_back(label_targets.at(handler.get_label()));
      }
    }
  }
}

/*******************************************************************	\

Function: goto_convertt::finish_gotos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::finish_gotos(goto_programt &dest, const irep_idt &mode)
{
  for(const auto &g_it : targets.gotos)
  {
    goto_programt::instructiont &i=*(g_it.first);

    if(i.is_start_thread())
    {
      const irep_idt &goto_label=i.code.get(ID_destination);

      labelst::const_iterator l_it=
        targets.labels.find(goto_label);

      if(l_it == targets.labels.end())
      {
        throw incorrect_goto_program_exceptiont(
          "goto label \'" + id2string(goto_label) + "\' not found",
          i.code.find_source_location());
      }

      i.targets.push_back(l_it->second.first);
    }
    else if(i.code.get_statement()==ID_goto)
    {
      const irep_idt &goto_label=i.code.get(ID_destination);

      labelst::const_iterator l_it=targets.labels.find(goto_label);

      if(l_it == targets.labels.end())
      {
        throw incorrect_goto_program_exceptiont(
          "goto label \'" + id2string(goto_label) + "\' not found",
          i.code.find_source_location());
      }

      i.complete_goto(l_it->second.first);

      // If the goto recorded a destructor stack, execute as much as is
      // appropriate for however many automatic variables leave scope.
      // We don't currently handle variables *entering* scope, which is illegal
      // for C++ non-pod types and impossible in Java in any case.
      auto goto_stack=g_it.second;
      const auto &label_stack=l_it->second.second;
      bool stack_is_prefix = label_stack.size() <= goto_stack.size();
      for(
        std::size_t idx = 0, ilim = label_stack.size();
        idx != ilim && stack_is_prefix; ++idx)
      {
        stack_is_prefix &= goto_stack[idx] == label_stack[idx];
      }

      if(!stack_is_prefix)
      {
          debug().source_location=i.code.find_source_location();
          debug() << "encountered goto `" << goto_label
                  << "' that enters one or more lexical blocks; "
                  << "omitting constructors and destructors" << eom;
      }
      else
      {
        auto unwind_to_size=label_stack.size();
        if(unwind_to_size<goto_stack.size())
        {
          debug().source_location=i.code.find_source_location();
          debug() << "adding goto-destructor code on jump to `"
                  << goto_label << "'" << eom;
          goto_programt destructor_code;
          unwind_destructor_stack(
            i.code.add_source_location(),
            unwind_to_size,
            destructor_code,
            goto_stack,
            mode);
          dest.destructive_insert(g_it.first, destructor_code);
          // This should leave iterators intact, as long as
          // goto_programt::instructionst is std::list.
        }
      }
    }
    else
    {
      UNREACHABLE;
    }
  }

  targets.gotos.clear();
}

void goto_convertt::finish_computed_gotos(goto_programt &goto_program)
{
  for(auto &g_it : targets.computed_gotos)
  {
    goto_programt::instructiont &i=*g_it;
    dereference_exprt destination = to_dereference_expr(i.code.op0());
    const exprt pointer = destination.pointer();

    // remember the expression for later checks
    i.type=OTHER;
    i.code=code_expressiont(pointer);

    // insert huge case-split
    for(const auto &label : targets.labels)
    {
      exprt label_expr(ID_label, empty_typet());
      label_expr.set(ID_identifier, label.first);

      const equal_exprt guard(pointer, address_of_exprt(label_expr));

      goto_programt::targett t=
        goto_program.insert_after(g_it);

      t->make_goto(label.second.first);
      t->source_location=i.source_location;
      t->guard=guard;
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
  for(const auto &i : dest.instructions)
    if(i.is_goto())
      i.get_target()->target_number = (++cnt);

  for(auto it = dest.instructions.begin(); it != dest.instructions.end(); it++)
  {
    if(!it->is_goto())
      continue;

    auto it_goto_y = std::next(it);

    if(
      it_goto_y == dest.instructions.end() || !it_goto_y->is_goto() ||
      !it_goto_y->guard.is_true() || it_goto_y->is_target())
      continue;

    auto it_z = std::next(it_goto_y);

    if(it_z == dest.instructions.end())
      continue;

    // cannot compare iterators, so compare target number instead
    if(it->get_target()->target_number == it_z->target_number)
    {
      it->set_target(it_goto_y->get_target());
      it->guard = boolean_negate(it->guard);
      it_goto_y->make_skip();
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
  goto_programt::targett t=dest.add_instruction(type);
  t->code=code;
  t->source_location=code.source_location();
}

void goto_convertt::convert_label(
  const code_labelt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  // grab the label
  const irep_idt &label=code.get_label();

  goto_programt tmp;

  // magic thread creation label.
  // The "__CPROVER_ASYNC_" signals the start of a sequence of instructions
  // that can be executed in parallel, i.e, a new thread.
  if(has_prefix(id2string(label), CPROVER_PREFIX "ASYNC_"))
  {
    // the body of the thread is expected to be
    // in the operand.
    DATA_INVARIANT(
      code.op0().is_not_nil(), "op0 in magic thread creation label is null");

    // replace the magic thread creation label with a
    // thread block (START_THREAD...END_THREAD).
    code_blockt thread_body;
    thread_body.add(to_code(code.op0()));
    thread_body.add_source_location()=code.source_location();
    generate_thread_block(thread_body, dest, mode);
  }
  else
  {
    convert(to_code(code.op0()), tmp, mode);

    goto_programt::targett target=tmp.instructions.begin();
    dest.destructive_append(tmp);

    targets.labels.insert({label, {target, targets.destructor_stack}});
    target->labels.push_front(label);
  }
}

void goto_convertt::convert_gcc_local_label(
  const codet &,
  goto_programt &)
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

  goto_programt::targett target=tmp.instructions.begin();
  dest.destructive_append(tmp);

  // is a default target given?

  if(code.is_default())
    targets.set_default(target);
  else
  {
    // cases?

    cases_mapt::iterator cases_entry=targets.cases_map.find(target);
    if(cases_entry==targets.cases_map.end())
    {
      targets.cases.push_back(std::make_pair(target, caset()));
      cases_entry=targets.cases_map.insert(std::make_pair(
            target, --targets.cases.end())).first;
    }

    exprt::operandst &case_op_dest=cases_entry->second->second;
    case_op_dest.push_back(code.case_op());
  }
}

void goto_convertt::convert_gcc_switch_case_range(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 3,
    "GCC's switch-case-range statement expected to have three operands",
    code.find_source_location());

  const auto lb = numeric_cast<mp_integer>(code.op0());
  const auto ub = numeric_cast<mp_integer>(code.op1());

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
  convert(to_code(code.op2()), tmp, mode);

  goto_programt::targett target = tmp.instructions.begin();
  dest.destructive_append(tmp);

  cases_mapt::iterator cases_entry = targets.cases_map.find(target);
  if(cases_entry == targets.cases_map.end())
  {
    targets.cases.push_back({target, caset()});
    cases_entry =
      targets.cases_map.insert({target, --targets.cases.end()}).first;
  }

  exprt::operandst &case_op_dest = cases_entry->second->second;

  for(mp_integer i = *lb; i <= *ub; ++i)
    case_op_dest.push_back(from_integer(i, code.op0().type()));
}

/// converts 'code' and appends the result to 'dest'
void goto_convertt::convert(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const irep_idt &statement=code.get_statement();

  if(statement==ID_block)
    convert_block(to_code_block(code), dest, mode);
  else if(statement==ID_decl)
    convert_decl(to_code_decl(code), dest, mode);
  else if(statement==ID_decl_type)
    convert_decl_type(code, dest);
  else if(statement==ID_expression)
    convert_expression(to_code_expression(code), dest, mode);
  else if(statement==ID_assign)
    convert_assign(to_code_assign(code), dest, mode);
  else if(statement==ID_assert)
    convert_assert(to_code_assert(code), dest, mode);
  else if(statement==ID_assume)
    convert_assume(to_code_assume(code), dest, mode);
  else if(statement==ID_function_call)
    convert_function_call(to_code_function_call(code), dest, mode);
  else if(statement==ID_label)
    convert_label(to_code_label(code), dest, mode);
  else if(statement==ID_gcc_local_label)
    convert_gcc_local_label(code, dest);
  else if(statement==ID_switch_case)
    convert_switch_case(to_code_switch_case(code), dest, mode);
  else if(statement==ID_gcc_switch_case_range)
    convert_gcc_switch_case_range(code, dest, mode);
  else if(statement==ID_for)
    convert_for(to_code_for(code), dest, mode);
  else if(statement==ID_while)
    convert_while(to_code_while(code), dest, mode);
  else if(statement==ID_dowhile)
    convert_dowhile(to_code_dowhile(code), dest, mode);
  else if(statement==ID_switch)
    convert_switch(to_code_switch(code), dest, mode);
  else if(statement==ID_break)
    convert_break(to_code_break(code), dest, mode);
  else if(statement==ID_return)
    convert_return(to_code_return(code), dest, mode);
  else if(statement==ID_continue)
    convert_continue(to_code_continue(code), dest, mode);
  else if(statement==ID_goto)
    convert_goto(to_code_goto(code), dest);
  else if(statement==ID_gcc_computed_goto)
    convert_gcc_computed_goto(code, dest);
  else if(statement==ID_skip)
    convert_skip(code, dest);
  else if(statement==ID_ifthenelse)
    convert_ifthenelse(to_code_ifthenelse(code), dest, mode);
  else if(statement==ID_start_thread)
    convert_start_thread(code, dest);
  else if(statement==ID_end_thread)
    convert_end_thread(code, dest);
  else if(statement==ID_atomic_begin)
    convert_atomic_begin(code, dest);
  else if(statement==ID_atomic_end)
    convert_atomic_end(code, dest);
  else if(statement==ID_cpp_delete ||
          statement=="cpp_delete[]")
    convert_cpp_delete(code, dest);
  else if(statement==ID_msc_try_except)
    convert_msc_try_except(code, dest, mode);
  else if(statement==ID_msc_try_finally)
    convert_msc_try_finally(code, dest, mode);
  else if(statement==ID_msc_leave)
    convert_msc_leave(code, dest, mode);
  else if(statement==ID_try_catch) // C++ try/catch
    convert_try_catch(code, dest, mode);
  else if(statement==ID_CPROVER_try_catch) // CPROVER-homemade
    convert_CPROVER_try_catch(code, dest, mode);
  else if(statement==ID_CPROVER_throw) // CPROVER-homemade
    convert_CPROVER_throw(code, dest, mode);
  else if(statement==ID_CPROVER_try_finally)
    convert_CPROVER_try_finally(code, dest, mode);
  else if(statement==ID_asm)
    convert_asm(to_code_asm(code), dest);
  else if(statement==ID_static_assert)
  {
    PRECONDITION(code.operands().size() == 2);
    exprt assertion=code.op0();
    assertion.make_typecast(bool_typet());
    simplify(assertion, ns);
    INVARIANT_WITH_DIAGNOSTICS(
      !assertion.is_false(),
      "static assertion " + id2string(get_string_constant(code.op1())),
      code.op0().find_source_location());
  }
  else if(statement==ID_dead)
    copy(code, DEAD, dest);
  else if(statement==ID_decl_block)
  {
    forall_operands(it, code)
      convert(to_code(*it), dest, mode);
  }
  else if(statement==ID_push_catch ||
          statement==ID_pop_catch ||
          statement==ID_exception_landingpad)
    copy(code, CATCH, dest);
  else
    copy(code, OTHER, dest);

  // make sure dest is never empty
  if(dest.instructions.empty())
  {
    dest.add_instruction(SKIP);
    dest.instructions.back().code.make_nil();
    dest.instructions.back().source_location=code.source_location();
  }
}

void goto_convertt::convert_block(
  const code_blockt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const source_locationt &end_location=code.end_location();

  // this saves the size of the destructor stack
  std::size_t old_stack_size=targets.destructor_stack.size();

  // now convert block
  for(const auto &b_code : code.statements())
    convert(b_code, dest, mode);

  // see if we need to do any destructors -- may have been processed
  // in a prior break/continue/return already, don't create dead code
  if(!dest.empty() &&
     dest.instructions.back().is_goto() &&
     dest.instructions.back().guard.is_true())
  {
    // don't do destructors when we are unreachable
  }
  else
    unwind_destructor_stack(end_location, old_stack_size, dest, mode);

  // remove those destructors
  targets.destructor_stack.resize(old_stack_size);
}

void goto_convertt::convert_expression(
  const code_expressiont &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt expr = code.expression();

  if(expr.id()==ID_if)
  {
    // We do a special treatment for c?t:f
    // by compiling to if(c) t; else f;
    const if_exprt &if_expr=to_if_expr(expr);
    code_ifthenelset tmp_code;
    tmp_code.add_source_location()=expr.source_location();
    tmp_code.cond()=if_expr.cond();
    tmp_code.then_case()=code_expressiont(if_expr.true_case());
    tmp_code.then_case().add_source_location()=expr.source_location();
    tmp_code.else_case()=code_expressiont(if_expr.false_case());
    tmp_code.else_case().add_source_location()=expr.source_location();
    convert_ifthenelse(tmp_code, dest, mode);
  }
  else
  {
    clean_expr(expr, dest, mode, false); // result _not_ used

    // Any residual expression?
    // We keep it to add checks later.
    if(expr.is_not_nil())
    {
      codet tmp=code;
      tmp.op0()=expr;
      tmp.add_source_location()=expr.source_location();
      copy(tmp, OTHER, dest);
    }
  }
}

void goto_convertt::convert_decl(
  const code_declt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  const irep_idt &identifier = code.get_identifier();

  const symbolt &symbol = ns.lookup(identifier);

  if(symbol.is_static_lifetime ||
     symbol.type.id()==ID_code)
    return; // this is a SKIP!

  if(code.operands().size()==1)
  {
    copy(code, DECL, dest);
  }
  else
  {
    // this is expected to go away
    exprt initializer;

    codet tmp=code;
    initializer=code.op1();
    tmp.operands().resize(1);

    // Break up into decl and assignment.
    // Decl must be visible before initializer.
    copy(tmp, DECL, dest);

    code_assignt assign(code.op0(), initializer);
    assign.add_source_location()=tmp.source_location();

    convert_assign(assign, dest, mode);
  }

  // now create a 'dead' instruction -- will be added after the
  // destructor created below as unwind_destructor_stack pops off the
  // top of the destructor stack
  const symbol_exprt symbol_expr(symbol.name, symbol.type);

  {
    code_deadt code_dead(symbol_expr);
    targets.destructor_stack.push_back(code_dead);
  }

  // do destructor
  code_function_callt destructor=get_destructor(ns, symbol.type);

  if(destructor.is_not_nil())
  {
    // add "this"
    address_of_exprt this_expr(symbol_expr, pointer_type(symbol.type));
    destructor.arguments().push_back(this_expr);

    targets.destructor_stack.push_back(destructor);
  }
}

void goto_convertt::convert_decl_type(
  const codet &,
  goto_programt &)
{
  // we remove these
}

void goto_convertt::convert_assign(
  const code_assignt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt lhs=code.lhs(),
        rhs=code.rhs();

  clean_expr(lhs, dest, mode);

  if(rhs.id()==ID_side_effect &&
     rhs.get(ID_statement)==ID_function_call)
  {
    INVARIANT_WITH_DIAGNOSTICS(
      rhs.operands().size() == 2,
      "function_call sideeffect takes two operands",
      rhs.find_source_location());

    Forall_operands(it, rhs)
      clean_expr(*it, dest, mode);

    do_function_call(lhs, rhs.op0(), rhs.op1().operands(), dest, mode);
  }
  else if(rhs.id()==ID_side_effect &&
          (rhs.get(ID_statement)==ID_cpp_new ||
           rhs.get(ID_statement)==ID_cpp_new_array))
  {
    Forall_operands(it, rhs)
      clean_expr(*it, dest, mode);

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
    clean_expr(rhs, dest, mode);

    if(lhs.id() == ID_typecast)
    {
      DATA_INVARIANT(
        lhs.operands().size() == 1, "Typecast must have one operand");

      // add a typecast to the rhs
      exprt new_rhs = rhs;
      rhs.make_typecast(lhs.op0().type());

      // remove typecast from lhs
      exprt tmp = lhs.op0();
      lhs.swap(tmp);
    }

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
      clean_expr(*it, dest, mode);

    code_assignt new_assign(code);
    new_assign.lhs()=lhs;
    new_assign.rhs()=rhs;

    copy(new_assign, ASSIGN, dest);
  }
  else
  {
    // do everything else
    clean_expr(rhs, dest, mode);

    if(lhs.id()==ID_typecast)
    {
      // add a typecast to the rhs
      rhs.make_typecast(to_typecast_expr(lhs).op().type());

      // remove typecast from lhs
      exprt tmp=lhs.op0();
      lhs.swap(tmp);
    }

    code_assignt new_assign(code);
    new_assign.lhs()=lhs;
    new_assign.rhs()=rhs;

    copy(new_assign, ASSIGN, dest);
  }
}

void goto_convertt::convert_init(
  const codet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 2,
    "init statement takes two operands",
    code.find_source_location());

  // make it an assignment
  codet assignment=code;
  assignment.set_statement(ID_assign);

  convert(to_code_assign(assignment), dest, mode);
}

void goto_convertt::convert_cpp_delete(
  const codet &code,
  goto_programt &dest)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().size() == 1,
    "cpp_delete statement takes one operand",
    code.find_source_location());

  exprt tmp_op=code.op0();

  clean_expr(tmp_op, dest, ID_cpp);

  // we call the destructor, and then free
  const exprt &destructor=
    static_cast<const exprt &>(code.find(ID_destructor));

  irep_idt delete_identifier;

  if(code.get_statement()==ID_cpp_delete_array)
    delete_identifier="__delete_array";
  else if(code.get_statement()==ID_cpp_delete)
    delete_identifier="__delete";
  else
    UNREACHABLE;

  if(destructor.is_not_nil())
  {
    if(code.get_statement()==ID_cpp_delete_array)
    {
      // build loop
    }
    else if(code.get_statement()==ID_cpp_delete)
    {
      // just one object
      const dereference_exprt deref_op(tmp_op);

      codet tmp_code=to_code(destructor);
      replace_new_object(deref_op, tmp_code);
      convert(tmp_code, dest, ID_cpp);
    }
    else
      UNREACHABLE;
  }

  // now do "free"
  exprt delete_symbol=ns.lookup(delete_identifier).symbol_expr();

  DATA_INVARIANT(
    to_code_type(delete_symbol.type()).parameters().size() == 1,
    "delete statement takes 1 parameter");

  typet arg_type=
    to_code_type(delete_symbol.type()).parameters().front().type();

  code_function_callt delete_call(
    delete_symbol, {typecast_exprt(tmp_op, arg_type)});
  delete_call.add_source_location()=code.source_location();

  convert(delete_call, dest, ID_cpp);
}

void goto_convertt::convert_assert(
  const code_assertt &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt cond=code.assertion();

  clean_expr(cond, dest, mode);

  goto_programt::targett t=dest.add_instruction(ASSERT);
  t->guard.swap(cond);
  t->source_location=code.source_location();
  t->source_location.set(ID_property, ID_assertion);
  t->source_location.set("user-provided", true);
}

void goto_convertt::convert_skip(
  const codet &code,
  goto_programt &dest)
{
  goto_programt::targett t=dest.add_instruction(SKIP);
  t->source_location=code.source_location();
  t->code=code;
}

void goto_convertt::convert_assume(
  const code_assumet &code,
  goto_programt &dest,
  const irep_idt &mode)
{
  exprt op=code.assumption();

  clean_expr(op, dest, mode);

  goto_programt::targett t=dest.add_instruction(ASSUME);
  t->guard.swap(op);
  t->source_location=code.source_location();
}

void goto_convertt::convert_loop_invariant(
  const codet &code,
  goto_programt::targett loop,
  const irep_idt &mode)
{
  exprt invariant=
    static_cast<const exprt&>(code.find(ID_C_spec_loop_invariant));

  if(invariant.is_nil())
    return;

  goto_programt no_sideeffects;
  clean_expr(invariant, no_sideeffects, mode);

  INVARIANT_WITH_DIAGNOSTICS(
    no_sideeffects.instructions.empty(),
    "loop invariant is not side-effect free",
    code.find_source_location());

  PRECONDITION(loop->is_goto());
  loop->guard.add(ID_C_spec_loop_invariant).swap(invariant);
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
  // v: if(!c) goto z;
  // w: P;
  // x: B;               <-- continue target
  // y: goto u;
  // z: ;                <-- break target

  // A;
  if(code.init().is_not_nil())
    convert(to_code(code.init()), dest, mode);

  exprt cond=code.cond();

  goto_programt sideeffects;
  clean_expr(cond, sideeffects, mode);

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the u label
  goto_programt::targett u=sideeffects.instructions.begin();

  // do the v label
  goto_programt tmp_v;
  goto_programt::targett v=tmp_v.add_instruction();

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction(SKIP);
  z->source_location=code.source_location();

  // do the x label
  goto_programt tmp_x;

  if(code.iter().is_nil())
  {
    tmp_x.add_instruction(SKIP);
    tmp_x.instructions.back().source_location=code.source_location();
  }
  else
  {
    exprt tmp_B=code.iter();

    clean_expr(tmp_B, tmp_x, mode, false);

    if(tmp_x.instructions.empty())
    {
      tmp_x.add_instruction(SKIP);
      tmp_x.instructions.back().source_location=code.source_location();
    }
  }

  // optimize the v label
  if(sideeffects.instructions.empty())
    u=v;

  // set the targets
  targets.set_break(z);
  targets.set_continue(tmp_x.instructions.begin());

  // v: if(!c) goto z;
  v->make_goto(z);
  v->guard = boolean_negate(cond);
  v->source_location=cond.source_location();

  // do the w label
  goto_programt tmp_w;
  convert(code.body(), tmp_w, mode);

  // y: goto u;
  goto_programt tmp_y;
  goto_programt::targett y=tmp_y.add_instruction();
  y->make_goto(u);
  y->guard=true_exprt();
  y->source_location=code.source_location();

  // loop invariant
  convert_loop_invariant(code, y, mode);

  dest.destructive_append(sideeffects);
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
  const exprt &cond=code.cond();
  const source_locationt &source_location=code.source_location();

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
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  z->source_location=source_location;

  goto_programt tmp_branch;
  generate_conditional_branch(
    boolean_negate(cond), z, source_location, tmp_branch, mode);

  // do the v label
  goto_programt::targett v=tmp_branch.instructions.begin();

  // do the y label
  goto_programt tmp_y;
  goto_programt::targett y=tmp_y.add_instruction();

  // set the targets
  targets.set_break(z);
  targets.set_continue(y);

  // do the x label
  goto_programt tmp_x;
  convert(code.body(), tmp_x, mode);

  // y: if(c) goto v;
  y->make_goto(v);
  y->guard=true_exprt();
  y->source_location=code.source_location();

  // loop invariant
  convert_loop_invariant(code, y, mode);

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
  source_locationt condition_location=code.cond().find_source_location();

  exprt cond=code.cond();

  goto_programt sideeffects;
  clean_expr(cond, sideeffects, mode);

  //    do P while(c);
  //--------------------
  // w: P;
  // x: sideeffects in c   <-- continue target
  // y: if(c) goto w;
  // z: ;                  <-- break target

  // save break/continue targets
  break_continue_targetst old_targets(targets);

  // do the y label
  goto_programt tmp_y;
  goto_programt::targett y=tmp_y.add_instruction();

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  z->source_location=code.source_location();

  // do the x label
  goto_programt::targett x;
  if(sideeffects.instructions.empty())
    x=y;
  else
    x=sideeffects.instructions.begin();

  // set the targets
  targets.set_break(z);
  targets.set_continue(x);

  // do the w label
  goto_programt tmp_w;
  convert(code.body(), tmp_w, mode);
  goto_programt::targett w=tmp_w.instructions.begin();

  // y: if(c) goto w;
  y->make_goto(w);
  y->guard=cond;
  y->source_location=condition_location;

  // loop invariant
  convert_loop_invariant(code, y, mode);

  dest.destructive_append(tmp_w);
  dest.destructive_append(sideeffects);
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

  if(case_op.size() == 1)
    return equal_exprt(value, case_op.at(0));
  else
  {
    exprt dest = exprt(ID_or, bool_typet());
    dest.reserve_operands(case_op.size());

    forall_expr(it, case_op)
    {
      equal_exprt eq_expr;
      eq_expr.lhs() = value;
      eq_expr.rhs() = *it;
      dest.move_to_operands(eq_expr);
    }
    INVARIANT(
      case_op.size() == dest.operands().size(),
      "case guard conversion should preserve the number of cases");

    return dest;
  }
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
  dest.add_instruction()->make_location(
    code.source_location());

  // get the location of the end of the body, but
  // default to location of switch, if none
  source_locationt body_end_location=
    code.body().get_statement()==ID_block?
      to_code_block(code.body()).end_location():
      code.source_location();

  // do the value we switch over
  exprt argument=code.value();

  goto_programt sideeffects;
  clean_expr(argument, sideeffects, mode);

  // save break/default/cases targets
  break_switch_targetst old_targets(targets);

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  z->source_location=body_end_location;

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
  size_t case_number=1;
  for(auto &case_pair : targets.cases)
  {
    const caset &case_ops=case_pair.second;

    if (case_ops.empty())
      continue;

    exprt guard_expr=case_guard(argument, case_ops);

    source_locationt source_location=case_ops.front().find_source_location();
    source_location.set_case_number(std::to_string(case_number));
    case_number++;
    guard_expr.add_source_location()=source_location;

    goto_programt::targett x=tmp_cases.add_instruction();
    x->make_goto(case_pair.first);
    x->guard.swap(guard_expr);
    x->source_location=source_location;
  }

  {
    goto_programt::targett d_jump=tmp_cases.add_instruction();
    d_jump->make_goto(targets.default_target);
    d_jump->source_location=targets.default_target->source_location;
  }

  dest.destructive_append(sideeffects);
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
    code.source_location(), targets.break_stack_size, dest, mode);

  // add goto
  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.break_target);
  t->source_location=code.source_location();
}

void goto_convertt::convert_return(
  const code_returnt &code,
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

  code_returnt new_code(code);

  if(new_code.has_return_value())
  {
    bool result_is_used=
      new_code.return_value().type().id()!=ID_empty;

    goto_programt sideeffects;
    clean_expr(new_code.return_value(), sideeffects, mode, result_is_used);
    dest.destructive_append(sideeffects);

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

    // Now add a return node to set the return value.
    goto_programt::targett t=dest.add_instruction();
    t->make_return();
    t->code=new_code;
    t->source_location=new_code.source_location();
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
  unwind_destructor_stack(code.source_location(), 0, dest, mode);

  // add goto to end-of-function
  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.return_target, true_exprt());
  t->source_location=new_code.source_location();
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
    code.source_location(), targets.continue_stack_size, dest, mode);

  // add goto
  goto_programt::targett t=dest.add_instruction();
  t->make_goto(targets.continue_target);
  t->source_location=code.source_location();
}

void goto_convertt::convert_goto(const code_gotot &code, goto_programt &dest)
{
  // this instruction will be completed during post-processing
  goto_programt::targett t = dest.add_instruction();
  t->make_incomplete_goto(code);
  t->source_location=code.source_location();

  // remember it to do the target later
  targets.gotos.push_back(std::make_pair(t, targets.destructor_stack));
}

void goto_convertt::convert_gcc_computed_goto(
  const codet &code,
  goto_programt &dest)
{
  // this instruction will turn into OTHER during post-processing
  goto_programt::targett t=dest.add_instruction(NO_INSTRUCTION_TYPE);
  t->source_location=code.source_location();
  t->code=code;

  // remember it to do this later
  targets.computed_gotos.push_back(t);
}

void goto_convertt::convert_start_thread(
  const codet &code,
  goto_programt &dest)
{
  goto_programt::targett start_thread=
    dest.add_instruction(START_THREAD);
  start_thread->source_location=code.source_location();
  start_thread->code=code;

  // remember it to do target later
  targets.gotos.push_back(
    std::make_pair(start_thread, targets.destructor_stack));
}

void goto_convertt::convert_end_thread(
  const codet &code,
  goto_programt &dest)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().empty(),
    "end_thread expects no operands",
    code.find_source_location());

  copy(code, END_THREAD, dest);
}

void goto_convertt::convert_atomic_begin(
  const codet &code,
  goto_programt &dest)
{
  INVARIANT_WITH_DIAGNOSTICS(
    code.operands().empty(),
    "atomic_begin expects no operands",
    code.find_source_location());

  copy(code, ATOMIC_BEGIN, dest);
}

void goto_convertt::convert_atomic_end(
  const codet &code,
  goto_programt &dest)
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

  bool has_else=
    !code.else_case().is_nil();

  const source_locationt &source_location=code.source_location();

  // We do a bit of special treatment for && in the condition
  // in case cleaning would be needed otherwise.
  if(code.cond().id()==ID_and &&
     code.cond().operands().size()==2 &&
     (needs_cleaning(code.cond().op0()) || needs_cleaning(code.cond().op1())) &&
     !has_else)
  {
    // if(a && b) XX --> if(a) if(b) XX
    code_ifthenelset new_if0, new_if1;
    new_if0.cond()=code.cond().op0();
    new_if1.cond()=code.cond().op1();
    new_if0.add_source_location()=source_location;
    new_if1.add_source_location()=source_location;
    new_if1.then_case()=code.then_case();
    new_if0.then_case()=new_if1;
    return convert_ifthenelse(new_if0, dest, mode);
  }

  // convert 'then'-branch
  goto_programt tmp_then;
  convert(code.then_case(), tmp_then, mode);

  goto_programt tmp_else;

  if(has_else)
    convert(code.else_case(), tmp_else, mode);

  exprt tmp_guard=code.cond();
  clean_expr(tmp_guard, dest, mode);

  generate_ifthenelse(
    tmp_guard, tmp_then, tmp_else, source_location, dest, mode);
}

void goto_convertt::collect_operands(
  const exprt &expr,
  const irep_idt &id,
  std::list<exprt> &dest)
{
  if(expr.id()!=id)
  {
    dest.push_back(expr);
  }
  else
  {
    // left-to-right is important
    forall_operands(it, expr)
      collect_operands(*it, id, dest);
  }
}

/// This is (believed to be) faster than using std::list.size
/// \par parameters: Goto program 'g'
/// \return True if 'g' has one instruction
static inline bool is_size_one(const goto_programt &g)
{
  return (!g.instructions.empty()) &&
    ++g.instructions.begin()==g.instructions.end();
}

/// if(guard) true_case; else false_case;
void goto_convertt::generate_ifthenelse(
  const exprt &guard,
  goto_programt &true_case,
  goto_programt &false_case,
  const source_locationt &source_location,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(is_empty(true_case) &&
     is_empty(false_case))
  {
    // hmpf. Useless branch.
    goto_programt tmp_z;
    goto_programt::targett z=tmp_z.add_instruction();
    z->make_skip();
    goto_programt::targett v=dest.add_instruction();
    v->make_goto(z, guard);
    v->source_location=source_location;
    dest.destructive_append(tmp_z);
    return;
  }

  // do guarded assertions directly
  if(is_size_one(true_case) &&
     true_case.instructions.back().is_assert() &&
     true_case.instructions.back().guard.is_false() &&
     true_case.instructions.back().labels.empty())
  {
    // The above conjunction deliberately excludes the instance
    // if(some) { label: assert(false); }
    true_case.instructions.back().guard=boolean_negate(guard);
    dest.destructive_append(true_case);
    true_case.instructions.clear();
    if(
      is_empty(false_case) ||
      (is_size_one(false_case) &&
       is_skip(false_case, false_case.instructions.begin())))
      return;
  }

  // similarly, do guarded assertions directly
  if(is_size_one(false_case) &&
     false_case.instructions.back().is_assert() &&
     false_case.instructions.back().guard.is_false() &&
     false_case.instructions.back().labels.empty())
  {
    // The above conjunction deliberately excludes the instance
    // if(some) ... else { label: assert(false); }
    false_case.instructions.back().guard=guard;
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
    true_case.instructions.front().guard.is_false() &&
    true_case.instructions.front().labels.empty() &&
    true_case.instructions.back().labels.empty())
  {
    true_case.instructions.front().guard = boolean_negate(guard);
    true_case.instructions.erase(--true_case.instructions.end());
    dest.destructive_append(true_case);
    true_case.instructions.clear();

    return;
  }

  // Flip around if no 'true' case code.
  if(is_empty(true_case))
    return generate_ifthenelse(
      boolean_negate(guard),
      false_case,
      true_case,
      source_location,
      dest,
      mode);

  bool has_else=!is_empty(false_case);

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
  goto_programt::targett x=tmp_x.add_instruction();

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();
  // We deliberately don't set a location for 'z', it's a dummy
  // target.

  // y: Q;
  goto_programt tmp_y;
  goto_programt::targett y;
  if(has_else)
  {
    tmp_y.swap(false_case);
    y=tmp_y.instructions.begin();
  }

  // v: if(!c) goto z/y;
  goto_programt tmp_v;
  generate_conditional_branch(
    boolean_negate(guard), has_else ? y : z, source_location, tmp_v, mode);

  // w: P;
  goto_programt tmp_w;
  tmp_w.swap(true_case);

  // x: goto z;
  x->make_goto(z);
  CHECK_RETURN(!tmp_w.instructions.empty());
  x->source_location=tmp_w.instructions.back().source_location;

  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);

  if(has_else)
  {
    dest.destructive_append(tmp_x);
    dest.destructive_append(tmp_y);
  }

  dest.destructive_append(tmp_z);
}

/// if(guard) goto target;
static bool has_and_or(const exprt &expr)
{
  forall_operands(it, expr)
    if(has_and_or(*it))
      return true;

  if(expr.id()==ID_and || expr.id()==ID_or)
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
    goto_programt::targett target_false=tmp.add_instruction();
    target_false->make_skip();
    target_false->source_location=source_location;

    generate_conditional_branch(
      guard, target_true, target_false, source_location, dest, mode);

    dest.destructive_append(tmp);
  }
  else
  {
    // simple branch
    exprt cond=guard;
    clean_expr(cond, dest, mode);

    goto_programt tmp;
    goto_programt::targett g=tmp.add_instruction();
    g->make_goto(target_true);
    g->guard=cond;
    g->source_location=source_location;
    dest.destructive_append(tmp);
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
  if(guard.id()==ID_not)
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

  if(guard.id()==ID_and)
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

    goto_programt::targett t_true=dest.add_instruction();
    t_true->make_goto(target_true);
    t_true->guard=true_exprt();
    t_true->source_location=source_location;

    return;
  }
  else if(guard.id()==ID_or)
  {
    // turn
    //   if(a || b) goto target_true; else goto target_false;
    // into
    //   if(a) goto target_true;
    //   if(b) goto target_true;
    //   goto target_false;

    std::list<exprt> op;
    collect_operands(guard, guard.id(), op);

    for(const auto &expr : op)
      generate_conditional_branch(
        expr, target_true, source_location, dest, mode);

    goto_programt::targett t_false=dest.add_instruction();
    t_false->make_goto(target_false);
    t_false->guard=true_exprt();
    t_false->source_location=guard.source_location();

    return;
  }

  exprt cond=guard;
  clean_expr(cond, dest, mode);

  goto_programt::targett t_true=dest.add_instruction();
  t_true->make_goto(target_true);
  t_true->guard=cond;
  t_true->source_location=source_location;

  goto_programt::targett t_false=dest.add_instruction();
  t_false->make_goto(target_false);
  t_false->guard=true_exprt();
  t_false->source_location=source_location;
}

bool goto_convertt::get_string_constant(
  const exprt &expr,
  irep_idt &value)
{
  if(expr.id()==ID_typecast &&
     expr.operands().size()==1)
    return get_string_constant(expr.op0(), value);

  if(expr.id()==ID_address_of &&
     expr.operands().size()==1 &&
     expr.op0().id()==ID_index &&
     expr.op0().operands().size()==2)
  {
    exprt index_op=get_constant(expr.op0().op0());
    simplify(index_op, ns);

    if(index_op.id()==ID_string_constant)
      return value=index_op.get(ID_value), false;
    else if(index_op.id()==ID_array)
    {
      std::string result;
      forall_operands(it, index_op)
        if(it->is_constant())
        {
          const auto i = numeric_cast<std::size_t>(*it);
          if(!i.has_value())
            return true;

          if(i.value() != 0) // to skip terminating 0
            result += static_cast<char>(i.value());
        }

      return value=result, false;
    }
  }

  if(expr.id()==ID_string_constant)
    return value=expr.get(ID_value), false;

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
  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=
      ns.lookup(to_symbol_expr(expr));

    return symbol.value;
  }
  else if(expr.id()==ID_member)
  {
    exprt tmp=expr;
    tmp.op0()=get_constant(expr.op0());
    return tmp;
  }
  else if(expr.id()==ID_index)
  {
    exprt tmp=expr;
    tmp.op0()=get_constant(expr.op0());
    tmp.op1()=get_constant(expr.op1());
    return tmp;
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

  code_declt decl(new_symbol.symbol_expr());
  decl.add_source_location()=source_location;
  convert_decl(decl, dest, mode);

  return new_symbol;
}

void goto_convertt::make_temp_symbol(
  exprt &expr,
  const std::string &suffix,
  goto_programt &dest,
  const irep_idt &mode)
{
  const source_locationt source_location=expr.find_source_location();

  symbolt &new_symbol =
    new_tmp_symbol(expr.type(), suffix, dest, source_location, mode);

  code_assignt assignment;
  assignment.lhs()=new_symbol.symbol_expr();
  assignment.rhs()=expr;
  assignment.add_source_location()=source_location;

  convert(assignment, dest, mode);

  expr=new_symbol.symbol_expr();
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
  const symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find("main");

  DATA_INVARIANT(
    s_it != symbol_table.symbols.end(), "failed to find main symbol");

  const symbolt &symbol=s_it->second;

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

  goto_programt::targett c=body.add_instruction();
  c->make_skip();
  convert(thread_body, body, mode);

  goto_programt::targett e=postamble.add_instruction(END_THREAD);
  e->source_location=thread_body.source_location();
  goto_programt::targett z=postamble.add_instruction();
  z->make_skip();

  goto_programt::targett a=preamble.add_instruction(START_THREAD);
  a->source_location=thread_body.source_location();
  a->targets.push_back(c);
  goto_programt::targett b=preamble.add_instruction();
  b->source_location=thread_body.source_location();
  b->make_goto(z);

  dest.destructive_append(preamble);
  dest.destructive_append(body);
  dest.destructive_append(postamble);
}
