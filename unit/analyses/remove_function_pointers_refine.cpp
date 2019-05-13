/*******************************************************************\
 Module: Unit tests for module remove_function_pointers.refine_call_type

 Author: Diffblue Ltd.

 Date: May 2019

\*******************************************************************/

/// \file
/// Unit tests for module remove_function_pointers

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_code.h>

#include <goto-programs/collect_function_pointer_targets.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>

SCENARIO(
  "List potential targets works for ellipsis",
  "[core][goto-programs][list_potential_targets]")
{
  goto_modelt goto_model;
  // create one instance of the function type, they are all
  // going to have the same signature

  symbolt int_param;
  int_param.name = "int_param";
  int_param.mode = ID_C;
  int_param.type = signedbv_typet{32};
  goto_model.symbol_table.add(int_param);

  code_typet::parameterst parameters;
  parameters.emplace_back(signedbv_typet{32});
  parameters.back().set_identifier("int_param");
  auto func_empty_type = code_typet{{}, empty_typet{}};
  auto func_ellipsis_type = code_typet{{}, empty_typet{}};
  func_ellipsis_type.make_ellipsis();
  auto func_one_arg_type = code_typet{parameters, empty_typet{}};
  // create an empty code block, to act as the functions' body
  code_blockt func_body = code_blockt{};

  irep_idt f_name{"f"};

  // void f(...){};
  symbolt f;
  f.name = f_name;
  f.mode = ID_C;
  f.type = func_ellipsis_type; // takes anything
  f.value = func_body;
  goto_model.symbol_table.add(f);

  // void g(int){};
  symbolt g;
  g.name = "g";
  g.mode = ID_C;
  g.type = func_one_arg_type; // takes one int
  g.value = func_body;
  goto_model.symbol_table.add(g);

  // create array with function pointer elements
  array_typet fp_array_type(
    pointer_typet{func_ellipsis_type, 64}, from_integer(2, index_type()));
  array_exprt fp_array{{}, fp_array_type};

  fp_array.copy_to_operands(address_of_exprt{f.symbol_expr()});
  fp_array.copy_to_operands(address_of_exprt{g.symbol_expr()});

  // fpa = fparray {f1, f2};
  symbolt fpa;
  fpa.name = "fpa";
  fpa.mode = ID_C;
  fpa.type = fp_array_type;
  fpa.value = fp_array;

  goto_model.symbol_table.add(fpa);

  irep_idt fn_ptr_name{"fn_ptr"};

  // pointer to fn call
  symbolt fn_ptr;
  fn_ptr.name = fn_ptr_name;
  fn_ptr.mode = ID_C;
  fn_ptr.type = pointer_typet{func_ellipsis_type, 64};
  goto_model.symbol_table.add(fn_ptr);

  // symbol for indexing the array
  symbolt z;
  z.name = "z";
  z.mode = ID_C;
  z.type = index_type();
  goto_model.symbol_table.add(z);

  // create function with pointer function call instruction

  // void entry(){z; array; fn_ptr = array[z]; *fn_ptr(z)};
  symbolt entry;
  entry.name = "entry";
  entry.mode = ID_C;
  entry.type = func_empty_type;

  code_function_callt::argumentst arguments;
  arguments.emplace_back(z.symbol_expr());

  code_blockt entry_body{
    {// fn_ptr = array[z];
     code_assignt{fn_ptr.symbol_expr(),
                  index_exprt{fp_array,
                              z.symbol_expr(),
                              pointer_type(func_ellipsis_type)}},
     // *fn_ptr();
     code_function_callt{dereference_exprt{fn_ptr.symbol_expr()}, arguments}}};
  entry.value = entry_body;
  goto_model.symbol_table.add(entry);

  WHEN("list_potential_targets is run")
  {
    goto_convert(goto_model, null_message_handler);

    // goto convert removes ellipsis so we need to re-insert them
    auto &f_symbol = goto_model.symbol_table.get_writeable_ref(f_name);
    to_code_type(f_symbol.type).make_ellipsis();
    auto &fn_ptr_symbol =
      goto_model.symbol_table.get_writeable_ref(fn_ptr_name);
    to_code_type(fn_ptr_symbol.type.subtype()).make_ellipsis();

    auto &goto_functions = goto_model.goto_functions;
    for(auto &goto_function_pair : goto_functions.function_map)
    {
      auto &goto_function = goto_function_pair.second;
      auto &goto_program = goto_function.body;
      for(auto &instruction : goto_program.instructions)
      {
        if(instruction.is_function_call())
        {
          code_function_callt function_call = instruction.get_function_call();
          auto &function = to_dereference_expr(function_call.function());
          to_code_type(function.type()).make_ellipsis();
          instruction.set_function_call(function_call);
        }
      }
    }

    auto target_map = get_function_pointer_targets(
      null_message_handler, goto_model.goto_functions, goto_model.symbol_table);
    THEN("there should be 4 targets recognised")
    {
      REQUIRE(target_map.size() == 1);
      REQUIRE(target_map.begin()->second.second.size() == 2);
    }
  }
}
