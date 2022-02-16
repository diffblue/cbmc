/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_CLASS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_CLASS_H

#include <list>
#include <vector>
#include <unordered_set>

#include <util/message.h>
#include <util/namespace.h>
#include <util/replace_expr.h>
#include <util/std_code.h>

#include "allocate_objects.h"
#include "destructor_tree.h"
#include "goto_program.h"

class side_effect_expr_overflowt;

class goto_convertt:public messaget
{
public:
  void
  goto_convert(const codet &code, goto_programt &dest, const irep_idt &mode);

  goto_convertt(
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    ns(_symbol_table),
    tmp_symbol_prefix("goto_convertt")
  {
  }

  virtual ~goto_convertt()
  {
  }

protected:
  symbol_table_baset &symbol_table;
  namespacet ns;
  std::string tmp_symbol_prefix;
  lifetimet lifetime = lifetimet::STATIC_GLOBAL;

  void goto_convert_rec(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);

  //
  // tools for symbols
  //
  symbolt &new_tmp_symbol(
    const typet &type,
    const std::string &suffix,
    goto_programt &dest,
    const source_locationt &,
    const irep_idt &mode);

  symbol_exprt make_compound_literal(
    const exprt &expr,
    goto_programt &dest,
    const irep_idt &mode);

  //
  // translation of C expressions (with side effects)
  // into the program logic
  //

  void clean_expr(
    exprt &expr,
    goto_programt &dest,
    const irep_idt &mode,
    bool result_is_used = true);

  void
  clean_expr_address_of(exprt &expr, goto_programt &dest, const irep_idt &mode);

  static bool needs_cleaning(const exprt &expr);

  void make_temp_symbol(
    exprt &expr,
    const std::string &suffix,
    goto_programt &,
    const irep_idt &mode);

  void rewrite_boolean(exprt &dest);

  static bool has_function_call(const exprt &expr);

  void remove_side_effect(
    side_effect_exprt &expr,
    goto_programt &dest,
    const irep_idt &mode,
    bool result_is_used,
    bool address_taken);
  void remove_assignment(
    side_effect_exprt &expr,
    goto_programt &dest,
    bool result_is_used,
    bool address_taken,
    const irep_idt &mode);
  void remove_pre(
    side_effect_exprt &expr,
    goto_programt &dest,
    bool result_is_used,
    bool address_taken,
    const irep_idt &mode);
  void remove_post(
    side_effect_exprt &expr,
    goto_programt &dest,
    const irep_idt &mode,
    bool result_is_used);
  void remove_function_call(
    side_effect_expr_function_callt &expr,
    goto_programt &dest,
    const irep_idt &mode,
    bool result_is_used);
  void remove_cpp_new(
    side_effect_exprt &expr,
    goto_programt &dest,
    bool result_is_used);
  void remove_cpp_delete(
    side_effect_exprt &expr,
    goto_programt &dest);
  void remove_malloc(
    side_effect_exprt &expr,
    goto_programt &dest,
    const irep_idt &mode,
    bool result_is_used);
  void remove_temporary_object(
    side_effect_exprt &expr,
    goto_programt &dest);
  void remove_statement_expression(
    side_effect_exprt &expr,
    goto_programt &dest,
    const irep_idt &mode,
    bool result_is_used);
  void remove_gcc_conditional_expression(
    exprt &expr,
    goto_programt &dest,
    const irep_idt &mode);
  void remove_overflow(
    side_effect_expr_overflowt &expr,
    goto_programt &dest,
    bool result_is_used,
    const irep_idt &mode);

  virtual void do_cpp_new(
    const exprt &lhs,
    const side_effect_exprt &rhs,
    goto_programt &dest);

  void do_java_new(
    const exprt &lhs,
    const side_effect_exprt &rhs,
    goto_programt &dest);

  void do_java_new_array(
    const exprt &lhs,
    const side_effect_exprt &rhs,
    goto_programt &dest);

  static void replace_new_object(
    const exprt &object,
    exprt &dest);

  void cpp_new_initializer(
    const exprt &lhs,
    const side_effect_exprt &rhs,
    goto_programt &dest);

  //
  // function calls
  //

  virtual void do_function_call(
    const exprt &lhs,
    const exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest,
    const irep_idt &mode);

  virtual void do_function_call_if(
    const exprt &lhs,
    const if_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest,
    const irep_idt &mode);

  virtual void do_function_call_symbol(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest,
    const irep_idt &mode);

  virtual void do_function_call_symbol(const symbolt &)
  {
  }

  virtual void do_function_call_other(
    const exprt &lhs,
    const exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);

  //
  // conversion
  //
  void convert_block(
    const code_blockt &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_frontend_decl(
    const code_frontend_declt &,
    goto_programt &,
    const irep_idt &mode);
  void convert_decl_type(const codet &code, goto_programt &dest);
  void convert_expression(
    const code_expressiont &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_assign(
    const code_assignt &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_cpp_delete(const codet &code, goto_programt &dest);
  void convert_loop_contracts(
    const codet &code,
    goto_programt::targett loop,
    const irep_idt &mode);
  void
  convert_for(const code_fort &code, goto_programt &dest, const irep_idt &mode);
  void convert_while(
    const code_whilet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_dowhile(
    const code_dowhilet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_assume(
    const code_assumet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_assert(
    const code_assertt &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_switch(
    const code_switcht &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_break(
    const code_breakt &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_return(
    const code_frontend_returnt &,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_continue(
    const code_continuet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_ifthenelse(
    const code_ifthenelset &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_goto(const code_gotot &code, goto_programt &dest);
  void convert_gcc_computed_goto(const codet &code, goto_programt &dest);
  void convert_skip(const codet &code, goto_programt &dest);
  void convert_label(
    const code_labelt &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_gcc_local_label(const codet &code, goto_programt &dest);
  void convert_switch_case(
    const code_switch_caset &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_gcc_switch_case_range(
    const code_gcc_switch_case_ranget &,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_function_call(
    const code_function_callt &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_start_thread(const codet &code, goto_programt &dest);
  void convert_end_thread(const codet &code, goto_programt &dest);
  void convert_atomic_begin(const codet &code, goto_programt &dest);
  void convert_atomic_end(const codet &code, goto_programt &dest);
  void convert_msc_try_finally(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_msc_try_except(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_msc_leave(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_try_catch(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_CPROVER_try_catch(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_CPROVER_try_finally(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_CPROVER_throw(
    const codet &code,
    goto_programt &dest,
    const irep_idt &mode);
  void convert_asm(const code_asmt &code, goto_programt &dest);

  void convert(const codet &code, goto_programt &dest, const irep_idt &mode);

  void copy(
    const codet &code,
    goto_program_instruction_typet type,
    goto_programt &dest);

  //
  // exceptions
  //

  symbol_exprt exception_flag(const irep_idt &mode);

  void unwind_destructor_stack(
    const source_locationt &source_location,
    goto_programt &dest,
    const irep_idt &mode,
    optionalt<node_indext> destructor_start_point = {},
    optionalt<node_indext> destructor_end_point = {});

  //
  // gotos
  //

  void finish_gotos(goto_programt &dest, const irep_idt &mode);
  void finish_computed_gotos(goto_programt &dest);
  void optimize_guarded_gotos(goto_programt &dest);

  typedef std::map<irep_idt,
                   std::pair<goto_programt::targett, node_indext>>
    labelst;
  typedef std::list<std::pair<goto_programt::targett, node_indext>>
    gotost;
  typedef std::list<goto_programt::targett> computed_gotost;
  typedef exprt::operandst caset;
  typedef std::list<std::pair<goto_programt::targett, caset> > casest;
  typedef std::map<goto_programt::targett, casest::iterator> cases_mapt;

  struct targetst
  {
    bool return_set, has_return_value, break_set, continue_set,
         default_set, throw_set, leave_set;

    labelst labels;
    gotost gotos;
    computed_gotost computed_gotos;
    destructor_treet destructor_stack;

    casest cases;
    cases_mapt cases_map;

    goto_programt::targett return_target, break_target, continue_target,
      default_target, throw_target, leave_target;

    node_indext break_stack_node, continue_stack_node, throw_stack_node,
                leave_stack_node;

    targetst():
      return_set(false),
      has_return_value(false),
      break_set(false),
      continue_set(false),
      default_set(false),
      throw_set(false),
      leave_set(false),
      break_stack_node(),
      continue_stack_node(),
      throw_stack_node(),
      leave_stack_node()
    {
    }

    void set_break(goto_programt::targett _break_target)
    {
      break_set=true;
      break_target=_break_target;
      break_stack_node=destructor_stack.get_current_node();
    }

    void set_continue(goto_programt::targett _continue_target)
    {
      continue_set=true;
      continue_target=_continue_target;
      continue_stack_node=destructor_stack.get_current_node();
    }

    void set_default(goto_programt::targett _default_target)
    {
      default_set=true;
      default_target=_default_target;
    }

    void set_return(goto_programt::targett _return_target)
    {
      return_set=true;
      return_target=_return_target;
    }

    void set_throw(goto_programt::targett _throw_target)
    {
      throw_set=true;
      throw_target=_throw_target;
      throw_stack_node=destructor_stack.get_current_node();
    }

    void set_leave(goto_programt::targett _leave_target)
    {
      leave_set=true;
      leave_target=_leave_target;
      leave_stack_node=destructor_stack.get_current_node();
    }
  } targets;

  struct break_continue_targetst
  {
    // for 'while', 'for', 'dowhile'

    explicit break_continue_targetst(const targetst &targets)
    {
      break_set=targets.break_set;
      continue_set=targets.continue_set;
      break_target=targets.break_target;
      continue_target=targets.continue_target;
    }

    void restore(targetst &targets)
    {
      targets.break_set=break_set;
      targets.continue_set=continue_set;
      targets.break_target=break_target;
      targets.continue_target=continue_target;
    }

    goto_programt::targett break_target;
    goto_programt::targett continue_target;
    bool break_set, continue_set;
  };

  struct break_switch_targetst
  {
    // for 'switch'

    explicit break_switch_targetst(const targetst &targets)
    {
      break_set=targets.break_set;
      default_set=targets.default_set;
      break_target=targets.break_target;
      default_target=targets.default_target;
      break_stack_node=targets.destructor_stack.get_current_node();
      cases=targets.cases;
      cases_map=targets.cases_map;
    }

    void restore(targetst &targets)
    {
      targets.break_set=break_set;
      targets.default_set=default_set;
      targets.break_target=break_target;
      targets.default_target=default_target;
      targets.cases=cases;
      targets.cases_map=cases_map;
    }

    goto_programt::targett break_target;
    goto_programt::targett default_target;
    bool break_set, default_set;
    node_indext break_stack_node;

    casest cases;
    cases_mapt cases_map;
  };

  struct throw_targett
  {
    // for 'try...catch' and the like

    explicit throw_targett(const targetst &targets)
    {
      throw_set=targets.throw_set;
      throw_target=targets.throw_target;
      throw_stack_node=targets.destructor_stack.get_current_node();
    }

    void restore(targetst &targets)
    {
      targets.throw_set=throw_set;
      targets.throw_target=throw_target;
    }

    goto_programt::targett throw_target;
    bool throw_set;
    node_indext throw_stack_node;
  };

  struct leave_targett
  {
    // for 'try...leave...finally'

    explicit leave_targett(const targetst &targets)
    {
      leave_set=targets.leave_set;
      leave_target=targets.leave_target;
      leave_stack_node=targets.destructor_stack.get_current_node();
    }

    void restore(targetst &targets)
    {
      targets.leave_set=leave_set;
      targets.leave_target=leave_target;
    }

    goto_programt::targett leave_target;
    bool leave_set;
    node_indext leave_stack_node;
  };

  exprt case_guard(
    const exprt &value,
    const caset &case_op);

  // if(cond) { true_case } else { false_case }
  void generate_ifthenelse(
    const exprt &cond,
    goto_programt &true_case,
    goto_programt &false_case,
    const source_locationt &,
    goto_programt &dest,
    const irep_idt &mode);

  // if(guard) goto target_true; else goto target_false;
  void generate_conditional_branch(
    const exprt &guard,
    goto_programt::targett target_true,
    goto_programt::targett target_false,
    const source_locationt &,
    goto_programt &dest,
    const irep_idt &mode);

  // if(guard) goto target;
  void generate_conditional_branch(
    const exprt &guard,
    goto_programt::targett target_true,
    const source_locationt &,
    goto_programt &dest,
    const irep_idt &mode);

  // turn a OP b OP c into a list a, b, c
  static void collect_operands(
    const exprt &expr,
    const irep_idt &id,
    std::list<exprt> &dest);

  // START_THREAD; ... END_THREAD;
  void generate_thread_block(
    const code_blockt &thread_body,
    goto_programt &dest,
    const irep_idt &mode);

  //
  // misc
  //
  irep_idt get_string_constant(const exprt &expr);
  bool get_string_constant(const exprt &expr, irep_idt &);
  exprt get_constant(const exprt &expr);

  /// \brief Converts calls to the built in `enum_is_in_range` function to a
  ///    test that the given enum value is in the valid range of values for that
  ///    enum type.
  ///
  /// Note that the check for the range of values is done by creating a
  /// disjunction comparing the expression with each possible valid value.
  /// \param lhs: The destination for the generated assignment.
  /// \param function: The `enum_is_in_range` symbol of the source function call.
  /// \param arguments: A collection of arguments, which is expected to contain a
  ///    single argument which is an expression that resolves to a value of
  ///    enum type. The arguments are expected to have been prevalidated by the
  ///    typechecking process.
  /// \param dest: The goto program into which the generated assignment is
  ///    copied.
  void do_enum_is_in_range(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);

  // some built-in functions
  void do_atomic_begin(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_atomic_end(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_create_thread(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_array_equal(
    const exprt &lhs,
    const symbol_exprt &rhs,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_array_op(
    const irep_idt &id,
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_printf(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_scanf(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_input(
    const exprt &rhs,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_output(
    const exprt &rhs,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_prob_coin(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_prob_uniform(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  void do_havoc_slice(
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest,
    const irep_idt &mode);

  exprt get_array_argument(const exprt &src);
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_CLASS_H
