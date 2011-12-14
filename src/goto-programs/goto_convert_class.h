/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_CLASS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_CLASS_H

#include <list>

#include <namespace.h>
#include <replace_expr.h>
#include <guard.h>
#include <std_code.h>
#include <options.h>
#include <message_stream.h>

#include "goto_program.h"

class goto_convertt:public message_streamt
{
public:
  void goto_convert(const codet &code, goto_programt &dest);

  goto_convertt(
    contextt &_context,
    const optionst &_options,
    message_handlert &_message_handler):
    message_streamt(_message_handler),
    context(_context),
    options(_options),
    ns(_context),
    temporary_counter(0),
    tmp_symbol_prefix("goto_convertt::")
  {
  }
  
  virtual ~goto_convertt()
  {
  }
  
protected:
  contextt &context;
  const optionst &options;
  namespacet ns;
  unsigned temporary_counter;
  std::string tmp_symbol_prefix;

  void goto_convert_rec(const codet &code, goto_programt &dest);

  //
  // tools for symbols
  // 
  void new_name(symbolt &symbol);
  const symbolt &lookup(const irep_idt &identifier) const;
  
  symbolt &new_tmp_symbol(
    const typet &type,
    const std::string &suffix,
    goto_programt &dest,
    const locationt &location);
  
  typedef std::list<irep_idt> tmp_symbolst;
  tmp_symbolst tmp_symbols;

  //
  // translation of C expressions (with side effects)
  // into the program logic
  //
  
  void clean_expr(
    exprt &expr,
    goto_programt &dest,
    bool result_is_used=true);

  static bool needs_cleaning(const exprt &expr);
  
  void make_temp_symbol(
    exprt &expr,
    const std::string &suffix,
    goto_programt &dest);

  void address_of_replace_objects(
    exprt &expr,
    goto_programt &dest);

  void rewrite_boolean(exprt &dest);

  static bool has_sideeffect(const exprt &expr);
  static bool has_function_call(const exprt &expr);
  
  void remove_side_effect(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_assignment(side_effect_exprt &expr, goto_programt &dest);
  void remove_pre(side_effect_exprt &expr, goto_programt &dest);
  void remove_post(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_function_call(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_cpp_new(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_cpp_delete(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_malloc(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_temporary_object(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_statement_expression(side_effect_exprt &expr, goto_programt &dest, bool result_is_used);
  void remove_gcc_conditional_expression(exprt &expr, goto_programt &dest);

  virtual void do_cpp_new(
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
    goto_programt &dest);

  virtual void do_function_call_if(
    const exprt &lhs,
    const exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);

  virtual void do_function_call_symbol(
    const exprt &lhs,
    const exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);

  virtual void do_function_call_symbol(const symbolt &symbol)
  {
  }

  virtual void do_function_call_dereference(
    const exprt &lhs,
    const exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest);
  
  //
  // conversion
  //
  void convert_block(const codet &code, goto_programt &dest);
  void convert_decl(const code_declt &code, goto_programt &dest);
  void convert_decl_type(const codet &code, goto_programt &dest);
  void convert_expression(const code_expressiont &code, goto_programt &dest);
  void convert_assign(const code_assignt &code, goto_programt &dest);
  void convert_cpp_delete(const codet &code, goto_programt &dest);
  void convert_for(const codet &code, goto_programt &dest);
  void convert_while(const codet &code, goto_programt &dest);
  void convert_dowhile(const codet &code, goto_programt &dest);
  void convert_assume(const code_assumet &code, goto_programt &dest);
  void convert_assert(const code_assertt &code, goto_programt &dest);
  void convert_switch(const codet &code, goto_programt &dest);
  void convert_break(const code_breakt &code, goto_programt &dest);
  void convert_return(const code_returnt &code, goto_programt &dest);
  void convert_continue(const code_continuet &code, goto_programt &dest);
  void convert_ifthenelse(const codet &code, goto_programt &dest);
  void convert_init(const codet &code, goto_programt &dest);
  void convert_goto(const codet &code, goto_programt &dest);
  void convert_computed_goto(const codet &code, goto_programt &dest);
  void convert_skip(const codet &code, goto_programt &dest);
  void convert_non_deterministic_goto(const codet &code, goto_programt &dest);
  void convert_label(const code_labelt &code, goto_programt &dest);
  void convert_gcc_local_label(const codet &code, goto_programt &dest);
  void convert_function_call(const code_function_callt &code, goto_programt &dest);
  void convert_specc_notify(const codet &code, goto_programt &dest);
  void convert_specc_wait(const codet &code, goto_programt &dest);
  void convert_specc_par(const codet &code, goto_programt &dest);
  void convert_specc_event(const exprt &op,
                           std::set<irep_idt> &events);
  void convert_start_thread(const codet &code, goto_programt &dest);
  void convert_end_thread(const codet &code, goto_programt &dest);
  void convert_atomic_begin(const codet &code, goto_programt &dest);
  void convert_atomic_end(const codet &code, goto_programt &dest);
  void convert_bp_enforce(const codet &code, goto_programt &dest);
  void convert_bp_abortif(const codet &code, goto_programt &dest);
  void convert_msc_try_finally(const codet &code, goto_programt &dest);
  void convert_msc_try_except(const codet &code, goto_programt &dest);
  void convert_msc_leave(const codet &code, goto_programt &dest);
  void convert(const codet &code, goto_programt &dest);
  void copy(const codet &code, goto_program_instruction_typet type, goto_programt &dest);

  //
  // gotos
  //

  void finish_gotos();
  void finish_computed_gotos(goto_programt &dest);

  typedef std::map<irep_idt, goto_programt::targett> labelst;
  typedef std::list<goto_programt::targett> gotost;
  typedef std::list<goto_programt::targett> computed_gotost;
  typedef exprt::operandst caset;
  typedef std::list<std::pair<goto_programt::targett, caset> > casest;
  typedef std::map<goto_programt::targett, casest::iterator> cases_mapt;
  
  struct break_continue_targetst
  {
    break_continue_targetst():break_set(false), continue_set(false)
    {
    }
  
    goto_programt::targett break_target;
    bool break_set;

    goto_programt::targett continue_target;
    bool continue_set;
    
    void restore(const break_continue_targetst &targets)
    {
      *this=targets;
    }
  
    void set_break(goto_programt::targett _break_target)
    {
      break_set=true;
      break_target=_break_target;
    }

    void set_continue(goto_programt::targett _continue_target)
    {
      continue_set=true;
      continue_target=_continue_target;
    }
  };
  
  struct break_continue_switch_targetst:public break_continue_targetst
  {
    break_continue_switch_targetst():
      default_set(false)
    {
    }
    
    using break_continue_targetst::restore;
    
    void restore(const break_continue_switch_targetst &targets)
    {
      *this=targets;
    }
  
    void set_default(goto_programt::targett _default_target)
    {
      default_set=true;
      default_target=_default_target;
    }

    goto_programt::targett default_target;
    bool default_set;
    casest cases;
    cases_mapt cases_map;
  };

  struct targetst:public break_continue_switch_targetst
  {
    bool return_set;
    bool return_value;

    labelst labels;
    gotost gotos;
    computed_gotost computed_gotos;

    targetst():
      return_set(false)
    {
    }
    
    void swap(targetst &targets)
    {
      std::swap(targets.break_target, break_target);
      std::swap(targets.break_set, break_set);

      std::swap(targets.continue_target, continue_target);
      std::swap(targets.continue_set, continue_set);

      std::swap(targets.return_value, return_value);
      std::swap(targets.return_set, return_set);   
      
      std::swap(targets.default_target, default_target);
      std::swap(targets.default_set, default_set);
      
      targets.labels.swap(labels);
      targets.gotos.swap(gotos);
      targets.cases.swap(cases);
      targets.cases_map.swap(cases_map);
    }
  } targets;
  
  void case_guard(
    const exprt &value,
    const caset &case_op,
    exprt &dest);

  // if(cond) { true_case } else { false_case }
  void generate_ifthenelse(
    const exprt &cond,
    goto_programt &true_case,
    goto_programt &false_case,
    const locationt &location,
    goto_programt &dest);

  // if(guard) goto target_true; else goto target_false;
  void generate_conditional_branch(
    const exprt &guard,
    goto_programt::targett target_true,
    goto_programt::targett target_false,
    const locationt &location,
    goto_programt &dest);

  // if(guard) goto target;
  void generate_conditional_branch(
    const exprt &guard,
    goto_programt::targett target_true,
    const locationt &location,
    goto_programt &dest);
    
  // turn a OP b OP c into a list a, b, c
  static void collect_operands(
    const exprt &expr,
    const irep_idt &id,
    std::list<exprt> &dest);

  //
  // misc
  //
  const irep_idt get_string_constant(const exprt &expr);

  // some built-in functions    
  void do_atomic_begin  (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_atomic_end    (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_create_thread (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_array_set     (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_array_equal   (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_array_copy    (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_printf        (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_input         (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_output        (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_cover         (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_prob_coin     (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);
  void do_prob_uniform  (const exprt &lhs, const exprt &rhs, const exprt::operandst &arguments, goto_programt &dest);

  exprt get_array_argument(const exprt &src);
};

#endif
