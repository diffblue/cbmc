/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java String
        library are recognized by the PASS algorithm

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#ifndef CPROVER_PASS_PREPROCESS_H
#define CPROVER_PASS_PREPROCESS_H

#include <goto-programs/goto_model.h>
#include <util/message.h>

class pass_preprocesst:public messaget
{
 public:
  pass_preprocesst(symbol_tablet &, goto_functionst &, const namespacet &);
  
 private:
  symbol_tablet & symbol_table;
  goto_functionst & goto_functions;
  const namespacet & ns;
  std::map<exprt, exprt> string_builders;
  std::map<irep_idt, irep_idt> side_effect_functions;
  std::map<irep_idt, irep_idt> string_functions;

  exprt replace_string_literals(const exprt & );

  void make_string_function(goto_programt::instructionst::iterator &, irep_idt);
  void make_array_function(goto_programt::instructionst::iterator &, irep_idt);
  void make_string_function_of_assign(goto_programt::instructionst::iterator & i_it, irep_idt function_name);
  void make_string_function_call(goto_programt::instructionst::iterator & i_it, irep_idt function_name);
  void make_string_function_side_effect
    (goto_programt & goto_program, goto_programt::instructionst::iterator & i_it, 
     irep_idt function_name);

  bool has_java_string_type(const exprt &expr);
  void replace_string_calls(goto_functionst::function_mapt::iterator f_it);
  
};

#endif
