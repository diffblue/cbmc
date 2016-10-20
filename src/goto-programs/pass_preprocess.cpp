/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java String
        library are recognized by the PASS algorithm

Author: Romain Brenguier

Date:   September 2016

\*******************************************************************/

#include "pass_preprocess.h"

#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/pointer_offset_size.h>
#include <solvers/refinement/string_functions.h>
#include <solvers/refinement/string_expr.h>


void pass_preprocesst::make_string_function
(goto_programt::instructionst::iterator & i_it, irep_idt function_name) 
{
  // replace "lhs=s.charAt(x)" by "lhs=__CPROVER_uninterpreted_string_char_at(s,i)"
  // Warning: in pass_preprocess::make_string_function: 
  // we should introduce an intermediary variable for each argument
  code_function_callt &function_call=to_code_function_call(i_it->code);
  code_typet old_type=to_code_type(function_call.function().type());

  auxiliary_symbolt tmp_symbol;
  //tmp_symbol.base_name=base_name;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=function_name;
  // tmp_symbol.type=type;
  tmp_symbol.type=old_type;
  symbol_table.add(tmp_symbol);
  // make sure it is in the function map
  goto_functions.function_map[irep_idt(function_name)];
  
  function_application_exprt rhs;
  rhs.type()=old_type.return_type();
  rhs.add_source_location()=function_call.source_location();
  rhs.function()=symbol_exprt(function_name);
  for(unsigned i = 0; i < function_call.arguments().size(); i++)
    rhs.arguments().push_back(replace_string_literals(function_call.arguments()[i]));
  code_assignt assignment(function_call.lhs(), rhs);
  assignment.add_source_location()=function_call.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
}

void pass_preprocesst::make_array_function
(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
  code_function_callt &function_call=to_code_function_call(i_it->code);
  // replace "lhs=s.toCharArray()" by "lhs=MALLOC(struct java::array[char],s->length)"
  // we produce a malloc side-effect, which stays
  typet object_type = function_call.type();
  exprt object_size = size_of_expr(object_type, ns);

  if(object_size.is_nil())
  {
    error().source_location=function_call.lhs().find_source_location();
    error() << "do_java_new got nil object_size" << eom;
    throw 0;
  }

  side_effect_exprt malloc_expr(ID_malloc);
  malloc_expr.copy_to_operands(object_size);
  malloc_expr.type()=pointer_typet(object_type);

  //i_it = goto_program.insert_after(i_it);
  //i_it->make_assignment();
  //i_it->code=assignment2;
  //goto_programt::targett t_n=i_it.add_instruction(ASSIGN);
  i_it->make_assignment();
  i_it->code=code_assignt(function_call.lhs(), malloc_expr);
  i_it->source_location=function_call.source_location();
  
}

void pass_preprocesst::make_string_function_of_assign(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
  assert(i_it->is_assign());
  code_assignt &assign=to_code_assign(i_it->code);
  typet old_type=assign.rhs().type();

  auxiliary_symbolt tmp_symbol;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=function_name;
  symbol_table.add(tmp_symbol);
  
  exprt rhs = replace_string_literals(assign.rhs().op0());
  /*function_application_exprt rhs;
  rhs.type()=old_type;
  rhs.add_source_location()=assign.source_location();
  rhs.function()=symbol_exprt(function_name);
  rhs.arguments().push_back(address_of_exprt(assign.rhs().op0()));*/
  code_assignt assignment(assign.lhs(), rhs);
  assignment.add_source_location()=assign.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
  goto_functions.function_map[irep_idt(function_name)];
}

void pass_preprocesst::make_string_function_call
(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
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
  for(unsigned i = 1; i < function_call.arguments().size(); i++)
    rhs.arguments().push_back(replace_string_literals(function_call.arguments()[i]));
  code_assignt assignment(function_call.arguments()[0], rhs);
  assignment.add_source_location()=function_call.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
  // make sure it is in the function map
  goto_functions.function_map[irep_idt(function_name)];
}

void pass_preprocesst::make_string_function_side_effect
(goto_programt & goto_program, goto_programt::instructionst::iterator & i_it, 
 irep_idt function_name)
{
  // replace "s.append(x)" by "s=__CPROVER_uninterpreted_string_concat(s,x)"
  code_function_callt &function_call=to_code_function_call(i_it->code);
  code_typet old_type=to_code_type(function_call.function().type());

  auxiliary_symbolt tmp_symbol;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=function_name;
  symbol_table.add(tmp_symbol);
  
  function_application_exprt rhs;
  typet return_type = function_call.arguments()[0].type();
  rhs.type()=return_type;//to_pointer_type(return_type).subtype();
  rhs.add_source_location()=function_call.source_location();
  rhs.function()=symbol_exprt(function_name);
  for(unsigned i = 0; i < function_call.arguments().size(); i++)
    rhs.arguments().push_back(replace_string_literals(function_call.arguments()[i]));
  //code_assignt assignment(dereference_exprt(function_call.arguments()[0]), rhs);
  code_assignt assignment(function_call.arguments()[0], rhs);
  //code_assignt assignment2(function_call.lhs(), function_call.arguments()[0]);
  // add a mapping from the left hand side to the first argument
  string_builders[function_call.lhs()]=function_call.arguments()[0]; 
  assignment.add_source_location()=function_call.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
  // make sure it is in the function map
  goto_functions.function_map[irep_idt(function_name)];

  //i_it = goto_program.insert_after(i_it);
  //i_it->make_assignment();
  //i_it->code=assignment2;
  // add a mapping from the left hand side to the first argument
  //string_builders[function_call.lhs()]=function_call.arguments()[0]; 
}


bool pass_preprocesst::has_java_string_type(const exprt &expr)
{
  const typet type = expr.type();
  if(type.id() == ID_pointer) {
    pointer_typet pt = to_pointer_type(type);
    typet subtype = pt.subtype();
    if(subtype.id() == ID_symbol) {
      irep_idt tag = to_symbol_type(subtype).get_identifier();
      return (tag == irep_idt("java::java.lang.String"));
    } else return false;
  } else return false;
}


void pass_preprocesst::replace_string_calls
(goto_functionst::function_mapt::iterator f_it)
{
  goto_programt &goto_program=f_it->second.body;
  // map several names of a string builder to a unique one
  std::map<exprt, exprt> string_builders;
  
  Forall_goto_program_instructions(i_it, goto_program) {  
    if(i_it->is_function_call()) {

      code_function_callt &function_call=to_code_function_call(i_it->code);
      for(unsigned i = 0; i < function_call.arguments().size(); i++)
	if(string_builders.find(function_call.arguments()[i]) != string_builders.end())
	  function_call.arguments()[i]= string_builders[function_call.arguments()[i]];

      if(function_call.function().id()==ID_symbol){
	const irep_idt function_id=
	  to_symbol_expr(function_call.function()).get_identifier();
	  
	// Warning: this serie of tests should be reimplemented using a
	// map<irep_idt,irep_idt>

	if(function_id == irep_idt("java::java.lang.String.charAt:(I)C")
	   || function_id == irep_idt("java::java.lang.StringBuilder.charAt:(I)C")
	   || function_id == irep_idt("java::java.lang.CharSequence.charAt:(I)C")
	   ) {
	  make_string_function(i_it,cprover_string_char_at_func);

	} else if(function_id == irep_idt("java::java.lang.String.toCharArray:()[C")) {
	  make_array_function(i_it,cprover_string_to_char_array_func);
	} else if(string_functions.find(function_id) != string_functions.end()) 
	  {
	    make_string_function(i_it,string_function[function_id]);
	  }
	} else if(side_effect_functions.find(function_id) != side_effect_functions.end()) 
	  {
	    make_string_function_side_effect(goto_program, i_it,side_effect_functions[function_id]);
	  }
	else if(function_id == irep_idt
		("java::java.lang.String.<init>:(Ljava/lang/String;)V")
		|| function_id == irep_idt
		("java::java.lang.String.<init>:(Ljava/lang/StringBuilder;)V")) {
	  make_string_function_call(i_it, cprover_string_copy_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.StringBuilder.<init>:(Ljava/lang/String;)V")) {
	  make_string_function_call(i_it, cprover_string_copy_func);
	} else if(function_id == irep_idt("java::java.lang.String.<init>:()V")) {
	  make_string_function_call(i_it, cprover_string_empty_string_func);
	} else if(function_id == irep_idt("java::java.lang.StringBuilder.<init>:()V")) {
	  make_string_function_call(i_it, cprover_string_empty_string_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.Integer.toString:(I)Ljava/lang/String;")
		  || function_id == irep_idt
		  ("java::java.lang.String.valueOf:(I)Ljava/lang/String;")
		  ) {
	  make_string_function(i_it, cprover_string_of_int_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.Integer.toHexString:(I)Ljava/lang/String;")) {
	  make_string_function(i_it,  cprover_string_of_int_hex_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.String.valueOf:(L)Ljava/lang/String;")) {
	  make_string_function(i_it, cprover_string_of_long_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.String.valueOf:(F)Ljava/lang/String;")
		  ||function_id == irep_idt
		  ("java::java.lang.Float.toString:(F)Ljava/lang/String;")) {
	  make_string_function(i_it, cprover_string_of_float_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.String.valueOf:(D)Ljava/lang/String;")) {
	  make_string_function(i_it, cprover_string_of_double_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.String.valueOf:(Z)Ljava/lang/String;")) {
	  make_string_function(i_it, cprover_string_of_bool_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.String.valueOf:(C)Ljava/lang/String;")) {
	  make_string_function(i_it, cprover_string_of_char_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.Integer.parseInt:(Ljava/lang/String;)I")) {
	  make_string_function(i_it, cprover_string_parse_int_func);
	} else if(function_id == irep_idt
		  ("java::java.lang.String.valueOf:([CII)Ljava/lang/String;")
		  ||function_id == irep_idt
		  ("java::java.lang.String.valueOf:([C)Ljava/lang/String;")
		  ) {
	  make_string_function(i_it, cprover_string_value_of_func);
	} else if(function_id == irep_idt("java::java.lang.StringBuilder.toString:()Ljava/lang/String;")) {
	  make_string_function(i_it, cprover_string_copy_func);
	} else if(function_id == irep_idt("java::java.lang.StringBuilder.setLength:(I)V")) {
	  make_string_function_side_effect(goto_program, i_it,
					   cprover_string_set_length_func);
	} else if(function_id == irep_idt("java::java.lang.String.format:(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;")) {
	  make_string_function(i_it, cprover_string_format_func);
	}
      } 

    } else {
      if(i_it->is_assign()) {
	code_assignt assignment = to_code_assign(i_it->code);
	exprt new_rhs = replace_string_literals(assignment.rhs());
	code_assignt new_assignment(assignment.lhs(),new_rhs);
	new_assignment.add_source_location()=assignment.source_location();
	i_it->make_assignment();
	i_it->code=new_assignment;
      }
    }
  }
  return;
}

exprt pass_preprocesst::replace_string_literals(const exprt & expr) 
{
  if(has_java_string_type(expr) ) {
    if(expr.operands().size() == 1 && expr.op0().id() ==ID_symbol) {
      std::string id(to_symbol_expr(expr.op0()).get_identifier().c_str());
      if(id.substr(0,31) == "java::java.lang.String.Literal."){
	function_application_exprt rhs;
	rhs.type()=expr.type();
	rhs.add_source_location()=expr.source_location();
	rhs.function()=symbol_exprt(cprover_string_literal_func);
	goto_functions.function_map[cprover_string_literal_func];
	rhs.arguments().push_back(address_of_exprt(expr.op0()));
	auxiliary_symbolt tmp_symbol;
	tmp_symbol.is_static_lifetime=false;
	tmp_symbol.mode=ID_java;
	tmp_symbol.name=cprover_string_literal_func;
	symbol_table.add(tmp_symbol);
	return rhs;
      }
    }
  }
  return expr;
}


 pass_preprocesst::pass_preprocesst (symbol_tablet & _symbol_table, goto_functionst & _goto_functions, const namespacet & _ns)
   : symbol_table(_symbol_table),goto_functions(_goto_functions), ns(_ns)
 {

   // initialiasing the function maps
   string_functions[irep_idt("java::java.lang.String.codePointAt:(I)I")] = cprover_string_code_point_at_func;
   string_functions[irep_idt("java::java.lang.String.codePointBefore:(I)I")] = cprover_string_code_point_before_func;
   string_functions[irep_idt("java::java.lang.String.codePointCount:(II)I")] = cprover_string_code_point_count_func;
   string_functions[irep_idt("java::java.lang.String.offsetByCodePoints:(II)I")] = cprover_string_offset_by_code_point_func;
   string_functions[irep_idt("java::java.lang.String.hashCode:()I")] = cprover_string_hash_code_func;
   string_functions[irep_idt("java::java.lang.String.indexOf:(I)I")] = cprover_string_index_of_func;
   string_functions[irep_idt("java::java.lang.String.indexOf:(II)I")] = cprover_string_index_of_func;
   string_functions[irep_idt("java::java.lang.String.indexOf:(Ljava/lang/String;)I")] = cprover_string_index_of_func;
   string_functions[irep_idt("java::java.lang.String.indexOf:(Ljava/lang/String;I)I")] = cprover_string_index_of_func;
   string_functions[irep_idt("java::java.lang.String.lastIndexOf:(I)I")]=cprover_string_last_index_of_func;
   string_functions[irep_idt("java::java.lang.String.lastIndexOf:(II)I")]=cprover_string_last_index_of_func;
   string_functions[irep_idt("java::java.lang.String.lastIndexOf:(Ljava/lang/String;)I")]=cprover_string_last_index_of_func;
   string_functions[irep_idt("java::java.lang.String.lastIndexOf:(Ljava/lang/String;I)I")]=cprover_string_last_index_of_func;
   string_functions[irep_idt("java::java.lang.String.concat:(Ljava/lang/String;)Ljava/lang/String;")] = cprover_string_concat_func;
 string_functions[irep_idt("java::java.lang.String.length:()I")] = cprover_string_length_func;
 string_functions[irep_idt("java::java.lang.StringBuilder.length:()I")] = cprover_string_length_func;
 string_functions[irep_idt("java::java.lang.String.equals:(Ljava/lang/Object;)Z")] =
	  make_st cprover_string_equal_func;
 string_functions[irep_idt("java::java.lang.String.equalsIgnoreCase:(Ljava/lang/String;)Z")] = cprover_string_equals_ignore_case_func;
 } else if(function_id == irep_idt
		  ("java::java.lang.String.startsWith:(Ljava/lang/String;)Z")
		  || function_id == irep_idt
		  ("java::java.lang.String.startsWith:(Ljava/lang/String;I)Z")
		  ) {
	  make_string_function(i_it,cprover_string_startswith_func);
 string_functions[irep_idt("java::java.lang.String.endsWith:(Ljava/lang/String;)Z")] = cprover_string_endswith_func;
 string_functions[irep_idt("java::java.lang.String.substring:(II)Ljava/lang/String;")] = cprover_string_substring_func;
 } else if(function_id == irep_idt("java::java.lang.String.substring:(II)Ljava/lang/String;")
		  || function_id == irep_idt("java::java.lang.String.substring:(I)Ljava/lang/String;")
		  || function_id == irep_idt("java::java.lang.StringBuilder.substring:(II)Ljava/lang/String;")
		  || function_id == irep_idt("java::java.lang.StringBuilder.substring:(I)Ljava/lang/String;")
		  || function_id == irep_idt("java::java.lang.String.subSequence:(II)Ljava/lang/CharSequence;")
		  ) {
	  make_string_function(i_it,cprover_string_substring_func);
 string_functions[irep_idt("java::java.lang.String.trim:()Ljava/lang/String;")] = cprover_string_trim_func;
 string_functions[irep_idt("java::java.lang.String.toLowerCase:()Ljava/lang/String;")] = cprover_string_to_lower_case_func;
 string_functions[irep_idt("java::java.lang.String.toUpperCase:()Ljava/lang/String;")] = cprover_string_to_upper_case_func;
 string_functions[irep_idt("java::java.lang.String.replace:(CC)Ljava/lang/String;")] = cprover_string_replace_func;
 string_functions[irep_idt("java::java.lang.String.contains:(Ljava/lang/CharSequence;)Z")] = cprover_string_contains_func;
 string_functions[irep_idt("java::java.lang.String.compareTo:(Ljava/lang/String;)I")] = cprover_string_compare_to_func;
 string_functions[irep_idt("java::java.lang.String.intern:()Ljava/lang/String;")] = cprover_string_intern_func;
 string_functions[irep_idt("java::java.lang.String.isEmpty:()Z")] = cprover_string_is_empty_func;
 

   side_effect_functions[irep_idt("java::java.lang.StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")] = cprover_string_concat_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.setCharAt:(IC)V")] = cprover_string_char_set_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.append:(I)Ljava/lang/StringBuilder;")] = cprover_string_concat_int_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.append:(J)Ljava/lang/StringBuilder;")] = cprover_string_concat_long_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.append:(Z)Ljava/lang/StringBuilder;")] = cprover_string_concat_bool_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.append:(C)Ljava/lang/StringBuilder;")] = cprover_string_concat_char_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.append:(D)Ljava/lang/StringBuilder;")] = cprover_string_concat_double_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.append:(F)Ljava/lang/StringBuilder;")] = cprover_string_concat_float_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.appendCodePoint:(I)Ljava/lang/StringBuilder;")] = cprover_string_concat_code_point_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.delete:(II)Ljava/lang/StringBuilder;")] = cprover_string_delete_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.deleteCharAt:(I)Ljava/lang/StringBuilder;")] = cprover_string_delete_char_at_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.insert:(ILjava/lang/String;)Ljava/lang/StringBuilder;")] = cprover_string_insert_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.insert:(II)Ljava/lang/StringBuilder;")] = cprover_string_insert_int_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.insert:(IJ)Ljava/lang/StringBuilder;")] = cprover_string_insert_long_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.insert:(IC)Ljava/lang/StringBuilder;")] = cprover_string_insert_char_func;
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.insert:(IZ)Ljava/lang/StringBuilder;") ] = cprover_string_insert_bool_func;

  Forall_goto_functions(it, goto_functions)
  {
    replace_string_calls(it);
  }
}


