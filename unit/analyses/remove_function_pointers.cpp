/*******************************************************************\
 Module: Unit tests for module remove_function_pointers

 Author: Diffblue Ltd.

 Date: Apr 2019

\*******************************************************************/

/// \file
/// Unit tests for module remove_function_pointers

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_code.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/remove_function_pointers.h>

SCENARIO(
  "List potential targets works reliable",
  "[core][goto-programs][list_potential_targets]")
{
  goto_modelt goto_model;
  // create one instance of the function type, they are all
  // going to have the same signature
  typet func_type = code_typet{{}, empty_typet{}};
  // create an empty code block, to act as the functions' body
  code_blockt func_body = code_blockt{};

  // void f(){};
  symbolt f;
  f.name = "f";
  f.mode = ID_C;
  f.type = func_type; // void, takes no params
  f.value = func_body;
  goto_model.symbol_table.add(f);

  // void g(){};
  symbolt g;
  g.name = "g";
  g.mode = ID_C;
  g.type = func_type; // void, takes no params
  g.value = func_body;
  goto_model.symbol_table.add(g);

  // void h(){};
  symbolt h;
  h.name = "h";
  h.mode = ID_C;
  h.type = func_type; // void, takes no params
  h.value = func_body;
  goto_model.symbol_table.add(h);

  // void l(){};
  symbolt l;
  l.name = "l";
  l.mode = ID_C;
  l.type = func_type; // void, takes no params
  l.value = func_body;
  goto_model.symbol_table.add(l);

  // create array with function pointer elements
  array_typet fp_array_type(
    pointer_typet{func_type, 64}, from_integer(4, signed_int_type()));
  array_exprt fp_array{{}, fp_array_type};

  fp_array.copy_to_operands(address_of_exprt{f.symbol_expr()});
  fp_array.copy_to_operands(address_of_exprt{g.symbol_expr()});
  fp_array.copy_to_operands(address_of_exprt{h.symbol_expr()});
  fp_array.copy_to_operands(address_of_exprt{l.symbol_expr()});

  // f = fparray {f1, f2, f3, f4};
  symbolt fpa;
  fpa.name = "f";
  fpa.mode = ID_C;
  fpa.type = fp_array_type;
  fpa.value = fp_array;

  goto_model.symbol_table.add(fpa);

  // pointer to fn call
  symbolt fn_ptr;
  fn_ptr.name = "fn_ptr";
  fn_ptr.mode = ID_C;
  fn_ptr.type = pointer_typet{func_type, 64};
  goto_model.symbol_table.add(fn_ptr);

  // symbol for indexing the array
  symbolt z;
  z.name = "z";
  z.mode = ID_C;
  z.type = signed_int_type();
  goto_model.symbol_table.add(z);

  // create function with pointer function call instruction

  // void entry(){z; array; fn_ptr = array[z]; *fn_ptr()};
  symbolt entry;
  entry.name = "entry";
  entry.mode = ID_C;
  entry.type = func_type; // void, takes no params

  code_blockt entry_body{
    {// fn_ptr = array[z];
     code_assignt{
       fn_ptr.symbol_expr(),
       index_exprt{fp_array, z.symbol_expr(), pointer_type(func_type)}},
     // *fn_ptr();
     code_function_callt{dereference_exprt{fn_ptr.symbol_expr()}}}};
  entry.value = entry_body;
  goto_model.symbol_table.add(entry);

  WHEN("list_potential_targets is run")
  {
    goto_convert(goto_model, null_message_handler);
    auto target_map =
      get_function_pointer_targets(null_message_handler, goto_model);
    THEN("there should be 4 targets recognised")
    {
      REQUIRE(target_map.size() == 1);
      REQUIRE(target_map.begin()->second.size() == 4);
    }
  }
}
