/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java String
        library are recognized by the PASS algorithm

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "pass_preprocess.h"


void make_string_function(symbol_tablet & symbol_table, goto_functionst & goto_functions,
			  goto_programt::instructionst::iterator & i_it, irep_idt function_name){
  // replace "lhs=s.charAt(x)" by "lhs=__CPROVER_uninterpreted_string_char_at(s,i)"
	  
  //to_symbol_expr(function_call.function()).set_identifier(irep_idt("__CPROVER_uninterpreted_string_char_at"));

  code_function_callt &function_call=to_code_function_call(i_it->code);
  code_typet old_type=to_code_type(function_call.function().type());

  auxiliary_symbolt tmp_symbol;
  //tmp_symbol.base_name=base_name;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=function_name;
  // tmp_symbol.type=type;
  symbol_table.add(tmp_symbol);
  
  //debug() << "we should replace the function call by  function application?" << "see builtin_functions.cpp" << eom;
  
  function_application_exprt rhs;
  rhs.type()=old_type.return_type();
  rhs.add_source_location()=function_call.source_location();
  rhs.function()=symbol_exprt(function_name);
  rhs.arguments()=function_call.arguments();
  code_assignt assignment(function_call.lhs(), rhs);
  assignment.add_source_location()=function_call.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
  // make sure it is in the function map
  goto_functions.function_map[irep_idt(function_name)];
}

void make_string_function_call(symbol_tablet & symbol_table, goto_functionst & goto_functions,
			  goto_programt::instructionst::iterator & i_it, irep_idt function_name){
  // replace "s.init(x)" by "s=__CPROVER_uninterpreted_string_literal(x)"
  code_function_callt &function_call=to_code_function_call(i_it->code);
  code_typet old_type=to_code_type(function_call.function().type());

  auxiliary_symbolt tmp_symbol;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=function_name;
  symbol_table.add(tmp_symbol);
  
  function_application_exprt rhs;
  rhs.type()=function_call.arguments()[0].type();
  rhs.add_source_location()=function_call.source_location();
  rhs.function()=symbol_exprt(function_name);
  for(int i = 1; i < function_call.arguments().size(); i++)
    rhs.arguments().push_back(function_call.arguments()[i]);
  code_assignt assignment(function_call.arguments()[0], rhs);
  assignment.add_source_location()=function_call.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
  // make sure it is in the function map
  goto_functions.function_map[irep_idt(function_name)];
}

void replace_string_calls(symbol_tablet & symbol_table,goto_functionst & goto_functions,
  goto_functionst::function_mapt::iterator f_it)
{
  goto_programt &goto_program=f_it->second.body;
  
  Forall_goto_program_instructions(i_it, goto_program) {  
    if(i_it->is_function_call()) {
      code_function_callt &function_call=to_code_function_call(i_it->code);
      if(function_call.function().id()==ID_symbol){
	const irep_idt function_id=
	  to_symbol_expr(function_call.function()).get_identifier();
	  
	if(function_id == irep_idt("java::java.lang.String.charAt:(I)C")) {
	  make_string_function(symbol_table, goto_functions, i_it,"__CPROVER_uninterpreted_char_at");
	} else if(function_id == irep_idt("java::java.lang.String.indexOf:(I)I")) {
	  make_string_function(symbol_table, goto_functions, i_it,"__CPROVER_uninterpreted_strindexof");
	} else if(function_id == irep_idt("java::java.lang.String.concat:(Ljava/lang/String;)Ljava/lang/String;")) {
	  make_string_function(symbol_table, goto_functions, i_it,"__CPROVER_uninterpreted_strcat");
	} else if(function_id == irep_idt("java::java.lang.String.length:()I")) {
	  make_string_function(symbol_table, goto_functions, i_it,"__CPROVER_uninterpreted_strlen");
	} else if(function_id == irep_idt("java::java.lang.String.equals:(Ljava/lang/Object;)Z")) {
	  make_string_function(symbol_table, goto_functions, i_it,"__CPROVER_uninterpreted_string_equal");
	} else if(function_id == irep_idt("java::java.lang.String.<init>:(Ljava/lang/String;)V")) {
	  make_string_function_call(symbol_table, goto_functions, i_it,"__CPROVER_uninterpreted_string_literal");
	}
      } 
    }
  }
  return;
}

void pass_preprocess(symbol_tablet & symbol_table, goto_functionst & goto_functions){
  Forall_goto_functions(it, goto_functions)
  {
    replace_string_calls(symbol_table,goto_functions,it);
  }
}


