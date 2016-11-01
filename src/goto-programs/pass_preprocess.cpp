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

symbol_exprt pass_preprocesst::new_tmp_symbol
(const std::string &name, const typet &type)
{
  auxiliary_symbolt tmp_symbol;
  tmp_symbol.base_name=name;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=name;
  tmp_symbol.type=type;
  symbol_table.add(tmp_symbol);
  return symbol_exprt(name,type);
}

void pass_preprocesst::declare_function(irep_idt function_name, const typet &type)
{
  auxiliary_symbolt func_symbol;
  func_symbol.base_name=function_name;
  func_symbol.is_static_lifetime=false;
  func_symbol.mode=ID_java;
  func_symbol.name=function_name;
  func_symbol.type=type;
  symbol_table.add(func_symbol);
  goto_functions.function_map[function_name];
}

void pass_preprocesst::make_string_function
(goto_programt::instructionst::iterator & i_it, irep_idt function_name) 
{
  code_function_callt &function_call=to_code_function_call(i_it->code);
  code_typet function_type=to_code_type(function_call.function().type());
  declare_function(function_name,function_type);
  function_application_exprt rhs;
  rhs.type()=function_type.return_type();
  rhs.add_source_location()=function_call.source_location();
  rhs.function()=symbol_exprt(function_name);
  for(unsigned i = 0; i < function_call.arguments().size(); i++)
    rhs.arguments().push_back(replace_string_literals(function_call.arguments()[i]));
  code_assignt assignment(function_call.lhs(), rhs);
  assignment.add_source_location()=function_call.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
}

void pass_preprocesst::make_string_function_call
(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
  code_function_callt &function_call=to_code_function_call(i_it->code);
  code_typet function_type=to_code_type(function_call.function().type());
  declare_function(function_name,function_type);
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
}

void pass_preprocesst::make_string_function_side_effect
(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
  code_function_callt &function_call=to_code_function_call(i_it->code);
  code_typet function_type=to_code_type(function_call.function().type());
  declare_function(function_name,function_type);
  function_application_exprt rhs;
  typet return_type = function_call.arguments()[0].type();
  rhs.type()=return_type;
  rhs.add_source_location()=function_call.source_location();
  rhs.function()=symbol_exprt(function_name);
  for(unsigned i = 0; i < function_call.arguments().size(); i++)
    rhs.arguments().push_back(replace_string_literals(function_call.arguments()[i]));
  code_assignt assignment(function_call.arguments()[0], rhs);
  
  // add a mapping from the left hand side to the first argument
  string_builders[function_call.lhs()]=function_call.arguments()[0]; 
  assignment.add_source_location()=function_call.source_location();
  i_it->make_assignment();
  i_it->code=assignment;
}

void pass_preprocesst::make_to_char_array_function
(goto_programt & goto_program, goto_programt::instructionst::iterator & i_it)
{

  code_function_callt &function_call=to_code_function_call(i_it->code);
  if(function_call.lhs().type().id()!=ID_pointer)
    debug() << "pass_preprocesst::make_to_char_array_function: " 
	    << "the function call should return a pointer" << eom;

  typet object_type = function_call.lhs().type().subtype();
  exprt object_size = size_of_expr(object_type, ns);

  if(object_size.is_nil())
    debug() << "pass_preprocesst::make_to_char_array_function got nil object_size" << eom;

  auto location = function_call.source_location();
  std::vector<codet> new_code;

  side_effect_exprt malloc_expr(ID_malloc);
  malloc_expr.copy_to_operands(object_size);
  malloc_expr.type()=pointer_typet(object_type);
  malloc_expr.add_source_location()=location;

  assert(function_call.arguments().size() >= 1);
  exprt string_argument = replace_string_literals(function_call.arguments()[0]);
  typet string_argument_type = string_argument.type();

  // tmp_assign = MALLOC(struct java::array[reference],sizeof(s))
  symbol_exprt tmp_assign = new_tmp_symbol("tmp_assign", pointer_typet(object_type));
  code_assignt assign_malloc(tmp_assign, malloc_expr);
  new_code.push_back(assign_malloc);

  // tmp_assign->length = (int)__CPROVER_uninterpreted_string_length_func(s);
  declare_function(cprover_string_length_func,unsignedbv_typet(32));

  function_application_exprt call_to_length;
  call_to_length.type()=unsignedbv_typet(32);
  call_to_length.add_source_location()=location;
  call_to_length.function()=symbol_exprt(cprover_string_length_func);
  call_to_length.arguments().push_back(string_argument);

  const struct_typet &struct_type=to_struct_type(ns.follow(object_type));
  dereference_exprt deref(tmp_assign, object_type);
  member_exprt length(deref,struct_type.components()[1].get_name(), 
		      struct_type.components()[1].type());
  code_assignt assign_length(length,typecast_exprt(call_to_length,signedbv_typet(32)));
  new_code.push_back(assign_length);

  // tmp_assign->data = new data.type[length];
  assert(ns.follow(object_type).id()==ID_struct);
  member_exprt data(deref,struct_type.components()[2].get_name(), 
		    struct_type.components()[2].type());
  side_effect_exprt data_cpp_new_expr(ID_cpp_new_array, data.type());
  data_cpp_new_expr.set(ID_size, length);
  symbol_exprt tmp_data = new_tmp_symbol("tmp_data", struct_type.components()[2].type());
  new_code.push_back(code_assignt(data, data_cpp_new_expr));

  // tmp_assign->data = __CPROVER_uninterpreted_string_data_func(s,tmp_assing->data);
  declare_function(cprover_string_data_func,void_typet());
  function_application_exprt call_to_data;
  call_to_data.type()=void_typet();
  call_to_data.add_source_location()=location;
  call_to_data.function()=symbol_exprt(cprover_string_data_func);
  call_to_data.arguments().push_back(string_argument);
  call_to_data.arguments().push_back(data);
  call_to_data.arguments().push_back(dereference_exprt(data));
  
  exprt tmp_nil = new_tmp_symbol("tmp_nil", void_typet());
  new_code.push_back(code_assignt(tmp_nil,call_to_data));

  // return_tmp0 = tmp_assign
  new_code.push_back(code_assignt(function_call.lhs(), tmp_assign));

  //  putting the assignements into the program
  for(int i=0; i<new_code.size(); i++) 
    {
      assert(new_code[i].get_statement() == ID_assign);
      i_it->make_assignment();
      i_it->code=new_code[i];
      i_it->source_location=location;
      if(i<new_code.size()-1)
	i_it=goto_program.insert_after(i_it);
    }
}


void pass_preprocesst::make_of_char_array_function
(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
  code_function_callt &function_call=to_code_function_call(i_it->code);
  exprt arg = function_call.arguments()[0];
  auto location = function_call.source_location();
  typet object_type = arg.type().subtype();

  exprt array_size = member_exprt(dereference_exprt(arg,object_type)
				  ,"length",signedbv_typet(32));
  exprt data_pointer = member_exprt(dereference_exprt(arg,object_type),"data",
				    pointer_typet(pointer_typet(unsignedbv_typet(16))));
  exprt data = dereference_exprt(data_pointer, pointer_typet(unsignedbv_typet(16)));

  std::vector<exprt>::iterator it = function_call.arguments().begin();
  *it = array_size; 
  function_call.arguments().insert(++it,data);
  make_string_function(i_it,function_name);
}

void pass_preprocesst::make_of_char_array_function_call
(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
  code_function_callt &function_call=to_code_function_call(i_it->code);
  exprt arg = function_call.arguments()[1];
  auto location = function_call.source_location();
  typet object_type = arg.type().subtype();
  exprt array_size = member_exprt(dereference_exprt(arg,object_type)
				  ,"length",signedbv_typet(32));
  exprt data_pointer = member_exprt(dereference_exprt(arg,object_type),"data",
				    pointer_typet(pointer_typet(unsignedbv_typet(16))));
  exprt data = dereference_exprt(data_pointer, pointer_typet(unsignedbv_typet(16)));

  std::vector<exprt>::iterator it = function_call.arguments().begin();
  *(++it) = array_size; 
  function_call.arguments().insert(++it,data);
  make_string_function_call(i_it,function_name);
}

void pass_preprocesst::make_of_char_array_side_effect
(goto_programt::instructionst::iterator & i_it, irep_idt function_name)
{
  code_function_callt &function_call=to_code_function_call(i_it->code);
  exprt arg = function_call.arguments()[2];
  auto location = function_call.source_location();
  typet object_type = arg.type().subtype();
  exprt array_size = member_exprt(dereference_exprt(arg,object_type)
				  ,"length",signedbv_typet(32));
  exprt data_pointer = member_exprt(dereference_exprt(arg,object_type),"data",
				    pointer_typet(pointer_typet(unsignedbv_typet(16))));
  exprt data = dereference_exprt(data_pointer, pointer_typet(unsignedbv_typet(16)));

  std::vector<exprt>::iterator it = std::next(std::next(function_call.arguments().begin()));
  *it = array_size; 
  function_call.arguments().insert(++it,data);
  make_string_function_side_effect(i_it,function_name);
}


void pass_preprocesst::replace_string_calls
(goto_functionst::function_mapt::iterator f_it)
{
  goto_programt &goto_program=f_it->second.body;
  
  Forall_goto_program_instructions(i_it, goto_program) 
    {  
      if(i_it->is_function_call()) 
	{
	  
	  code_function_callt &function_call=to_code_function_call(i_it->code);
	  for(unsigned i = 0; i < function_call.arguments().size(); i++)
	    if(string_builders.find(function_call.arguments()[i]) != string_builders.end())
	      function_call.arguments()[i]= string_builders[function_call.arguments()[i]];
	  
	  if(function_call.function().id()==ID_symbol)
	    {
	      const irep_idt function_id=
		to_symbol_expr(function_call.function()).get_identifier();
	      
	      if(string_functions.find(function_id) != string_functions.end())
		make_string_function(i_it,string_functions[function_id]);
	      else if(side_effect_functions.find(function_id) != side_effect_functions.end()) 
		make_string_function_side_effect(i_it,side_effect_functions[function_id]);
	      else if(string_function_calls.find(function_id) != string_function_calls.end()) 
		make_string_function_call(i_it, string_function_calls[function_id]);
	      else if(string_of_char_array_functions.find(function_id) != string_of_char_array_functions.end())
		make_of_char_array_function(i_it,string_of_char_array_functions[function_id]);
	      else if(string_of_char_array_function_calls.find(function_id) != string_of_char_array_function_calls.end())
		make_of_char_array_function_call(i_it,string_of_char_array_function_calls[function_id]);
	      else if(side_effect_char_array_functions.find(function_id) != side_effect_char_array_functions.end())
		make_of_char_array_side_effect(i_it,side_effect_char_array_functions[function_id]);
	      else if(function_id == irep_idt("java::java.lang.String.toCharArray:()[C")) 
		make_to_char_array_function(goto_program,i_it);
	    } 
	} 
      else
	{
	  if(i_it->is_assign()) 
	    {
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

exprt pass_preprocesst::replace_string_literals(const exprt & expr) 
{
  if(has_java_string_type(expr) ) 
    {
      if(expr.operands().size() == 1 && expr.op0().id() ==ID_symbol) 
	{
	  std::string id(to_symbol_expr(expr.op0()).get_identifier().c_str());
	  if(id.substr(0,31) == "java::java.lang.String.Literal.")
	    {
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

pass_preprocesst::pass_preprocesst (symbol_tablet & _symbol_table, goto_functionst & _goto_functions,
				    message_handlert &_message_handler):
  messaget(_message_handler), symbol_table(_symbol_table), ns(_symbol_table),
  goto_functions(_goto_functions)
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
   string_functions[irep_idt("java::java.lang.String.equals:(Ljava/lang/Object;)Z")] = cprover_string_equal_func;
   string_functions[irep_idt("java::java.lang.String.equalsIgnoreCase:(Ljava/lang/String;)Z")] = cprover_string_equals_ignore_case_func;
   string_functions[irep_idt("java::java.lang.String.startsWith:(Ljava/lang/String;)Z")] = cprover_string_startswith_func;
   string_functions[irep_idt ("java::java.lang.String.startsWith:(Ljava/lang/String;I)Z")] = cprover_string_startswith_func;
   string_functions[irep_idt("java::java.lang.String.endsWith:(Ljava/lang/String;)Z")] = cprover_string_endswith_func;
   string_functions[irep_idt("java::java.lang.String.substring:(II)Ljava/lang/String;")] = cprover_string_substring_func;
   string_functions[irep_idt("java::java.lang.String.substring:(II)Ljava/lang/String;")] = cprover_string_substring_func;
   string_functions[irep_idt("java::java.lang.String.substring:(I)Ljava/lang/String;")] = cprover_string_substring_func;
   string_functions[irep_idt("java::java.lang.StringBuilder.substring:(II)Ljava/lang/String;")] = cprover_string_substring_func;
   string_functions[irep_idt("java::java.lang.StringBuilder.substring:(I)Ljava/lang/String;")] = cprover_string_substring_func;
   string_functions[irep_idt("java::java.lang.String.subSequence:(II)Ljava/lang/CharSequence;")] = cprover_string_substring_func;
   string_functions[irep_idt("java::java.lang.String.trim:()Ljava/lang/String;")] = cprover_string_trim_func;
   string_functions[irep_idt("java::java.lang.String.toLowerCase:()Ljava/lang/String;")] = cprover_string_to_lower_case_func;
   string_functions[irep_idt("java::java.lang.String.toUpperCase:()Ljava/lang/String;")] = cprover_string_to_upper_case_func;
   string_functions[irep_idt("java::java.lang.String.replace:(CC)Ljava/lang/String;")] = cprover_string_replace_func;
   string_functions[irep_idt("java::java.lang.String.contains:(Ljava/lang/CharSequence;)Z")] = cprover_string_contains_func;
   string_functions[irep_idt("java::java.lang.String.compareTo:(Ljava/lang/String;)I")] = cprover_string_compare_to_func;
   string_functions[irep_idt("java::java.lang.String.intern:()Ljava/lang/String;")] = cprover_string_intern_func;
   string_functions[irep_idt("java::java.lang.String.isEmpty:()Z")] = cprover_string_is_empty_func;
   string_functions[irep_idt("java::java.lang.String.charAt:(I)C")] = cprover_string_char_at_func;
   string_functions[irep_idt("java::java.lang.StringBuilder.charAt:(I)C")] = cprover_string_char_at_func;
   string_functions[irep_idt("java::java.lang.CharSequence.charAt:(I)C")] = cprover_string_char_at_func;
   string_functions[irep_idt("java::java.lang.StringBuilder.toString:()Ljava/lang/String;")] = cprover_string_copy_func;

   string_functions[irep_idt("java::java.lang.String.valueOf:(F)Ljava/lang/String;")] = cprover_string_of_float_func;
   string_functions[irep_idt("java::java.lang.Float.toString:(F)Ljava/lang/String;")] = cprover_string_of_float_func;
   string_functions[irep_idt("java::java.lang.Integer.toString:(I)Ljava/lang/String;")] = cprover_string_of_int_func;
   string_functions[irep_idt("java::java.lang.String.valueOf:(I)Ljava/lang/String;")] = cprover_string_of_int_func;
   string_functions[irep_idt("java::java.lang.Integer.toHexString:(I)Ljava/lang/String;")] = cprover_string_of_int_hex_func;
   string_functions[irep_idt("java::java.lang.String.valueOf:(L)Ljava/lang/String;")] = cprover_string_of_long_func;
   string_functions[irep_idt("java::java.lang.String.valueOf:(D)Ljava/lang/String;")] = cprover_string_of_double_func;
   string_functions[irep_idt("java::java.lang.String.valueOf:(Z)Ljava/lang/String;")] = cprover_string_of_bool_func;
   string_functions[irep_idt("java::java.lang.String.valueOf:(C)Ljava/lang/String;")] = cprover_string_of_char_func;
   string_functions[irep_idt("java::java.lang.Integer.parseInt:(Ljava/lang/String;)I")] = cprover_string_parse_int_func;

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
   side_effect_functions[irep_idt("java::java.lang.StringBuilder.setLength:(I)V")] = cprover_string_set_length_func;


   side_effect_char_array_functions[irep_idt("java::java.lang.StringBuilder.insert:(I[CII)Ljava/lang/StringBuilder;")] =  cprover_string_insert_char_array_func;
   side_effect_char_array_functions[irep_idt("java::java.lang.StringBuilder.insert:(I[C)Ljava/lang/StringBuilder;")] =  cprover_string_insert_char_array_func;

   string_function_calls[irep_idt("java::java.lang.String.<init>:(Ljava/lang/String;)V")] = cprover_string_copy_func;
   string_function_calls[irep_idt("java::java.lang.String.<init>:(Ljava/lang/StringBuilder;)V")] = cprover_string_copy_func;
   string_function_calls[irep_idt("java::java.lang.StringBuilder.<init>:(Ljava/lang/String;)V")] = cprover_string_copy_func;
   string_function_calls[irep_idt("java::java.lang.String.<init>:()V")] = cprover_string_empty_string_func;
   string_function_calls[irep_idt("java::java.lang.StringBuilder.<init>:()V")] = cprover_string_empty_string_func;
   
   string_of_char_array_function_calls[irep_idt("java::java.lang.String.<init>:([C)V")] = cprover_string_of_char_array_func;
   string_of_char_array_function_calls[irep_idt("java::java.lang.String.<init>:([CII)V")] = cprover_string_of_char_array_func;
   string_of_char_array_functions[irep_idt("java::java.lang.String.valueOf:([CII)Ljava/lang/String;")] = cprover_string_of_char_array_func;
   string_of_char_array_functions[irep_idt("java::java.lang.String.valueOf:([C)Ljava/lang/String;")] = cprover_string_of_char_array_func;
   string_of_char_array_functions[irep_idt("java::java.lang.String.copyValueOf:([CII)Ljava/lang/String;")] = cprover_string_of_char_array_func;
   string_of_char_array_functions[irep_idt("java::java.lang.String.copyValueOf:([C)Ljava/lang/String;")] = cprover_string_of_char_array_func;

  Forall_goto_functions(it, goto_functions)
    replace_string_calls(it);
 }


