/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#include "c_nondet_symbol_factory.h"

#include <ansi-c/c_object_factory_parameters.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/nondet_bool.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include <goto-programs/allocate_objects.h>
#include <goto-programs/goto_functions.h>

/// Creates a nondet for expr, including calling itself recursively to make
/// appropriate symbols to point to if expr is a pointer.
/// \param assignments: The code block to add code to
/// \param expr: The expression which we are generating a non-determinate value
///   for
/// \param depth number of pointers followed so far during initialisation
/// \param recursion_set names of structs seen so far on current pointer chain
/// \param assign_const Indicates whether const objects should be nondet
///   initialized
void symbol_factoryt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr,
  const std::size_t depth,
  recursion_sett recursion_set,
  const bool assign_const)
{
  const typet &type = expr.type();

  if(!assign_const && expr.type().get_bool(ID_C_constant))
  {
    return;
  }

  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &base_type = pointer_type.base_type();

    if(base_type.id() == ID_code)
    {
      // Handle the pointer-to-code case separately:
      // leave as nondet_ptr to allow `remove_function_pointers`
      // to replace the pointer.
      assignments.add(code_frontend_assignt{
        expr, side_effect_expr_nondett{pointer_type, loc}});
      return;
    }

    if(base_type.id() == ID_struct_tag)
    {
      const irep_idt struct_tag =
        to_struct_tag_type(base_type).get_identifier();

      if(
        recursion_set.find(struct_tag) != recursion_set.end() &&
        depth >= object_factory_params.max_nondet_tree_depth)
      {
        assignments.add(
          code_frontend_assignt{expr, null_pointer_exprt{pointer_type}, loc});

        return;
      }
    }

    code_blockt non_null_inst;

    typet object_type = base_type;
    if(object_type.id() == ID_empty)
      object_type = char_type();

    exprt init_expr = allocate_objects.allocate_object(
      non_null_inst, expr, object_type, lifetime);

    gen_nondet_init(non_null_inst, init_expr, depth + 1, recursion_set, true);

    if(depth < object_factory_params.min_null_tree_depth)
    {
      // Add the following code to assignments:
      // <expr> = <aoe>;
      assignments.append(non_null_inst);
    }
    else
    {
      // Add the following code to assignments:
      //           IF !NONDET(_Bool) THEN GOTO <label1>
      //           <expr> = <null pointer>
      //           GOTO <label2>
      // <label1>: <expr> = &tmp$<temporary_counter>;
      //           <code from recursive call to gen_nondet_init() with
      //             tmp$<temporary_counter>>
      // And the next line is labelled label2
      const code_frontend_assignt set_null_inst{
        expr, null_pointer_exprt{pointer_type}, loc};

      code_ifthenelset null_check(
        side_effect_expr_nondett(bool_typet(), loc),
        std::move(set_null_inst),
        std::move(non_null_inst));

      assignments.add(std::move(null_check));
    }
  }
  else if(type.id() == ID_struct_tag)
  {
    const auto &struct_tag_type = to_struct_tag_type(type);

    const irep_idt struct_tag = struct_tag_type.get_identifier();

    recursion_set.insert(struct_tag);

    const auto &struct_type = to_struct_type(ns.follow_tag(struct_tag_type));

    for(const auto &component : struct_type.components())
    {
      const typet &component_type = component.type();

      if(!assign_const && component_type.get_bool(ID_C_constant))
      {
        continue;
      }

      const irep_idt name = component.get_name();

      member_exprt me(expr, name, component_type);
      me.add_source_location() = loc;

      gen_nondet_init(assignments, me, depth, recursion_set, assign_const);
    }
  }
  else if(type.id() == ID_array)
  {
    gen_nondet_array_init(assignments, expr, depth, recursion_set);
  }
  else
  {
    // If type is a ID_c_bool then add the following code to assignments:
    //   <expr> = NONDET(_BOOL);
    // Else add the following code to assignments:
    //   <expr> = NONDET(type);
    exprt rhs = type.id() == ID_c_bool ? get_nondet_bool(type, loc)
                                       : side_effect_expr_nondett(type, loc);
    code_frontend_assignt assign(expr, rhs);
    assign.add_source_location()=loc;

    assignments.add(std::move(assign));
  }
}

void symbol_factoryt::gen_nondet_array_init(
  code_blockt &assignments,
  const exprt &expr,
  std::size_t depth,
  const recursion_sett &recursion_set)
{
  auto const &array_type = to_array_type(expr.type());
  const auto &size = array_type.size();
  PRECONDITION(size.id() == ID_constant);
  auto const array_size = numeric_cast_v<size_t>(to_constant_expr(size));
  DATA_INVARIANT(array_size > 0, "Arrays should have positive size");
  for(size_t index = 0; index < array_size; ++index)
  {
    gen_nondet_init(
      assignments,
      index_exprt(expr, from_integer(index, size_type())),
      depth,
      recursion_set);
  }
}

/// Creates a symbol and generates code so that it can vary over all possible
/// values for its type. For pointers this involves allocating symbols which it
/// can point to.
/// \param init_code: The code block to add generated code to
/// \param symbol_table: The symbol table
/// \param base_name: The name to use for the symbol created
/// \param type: The type for the symbol created
/// \param loc: The location to assign to generated code
/// \param object_factory_parameters: configuration parameters for the object
///   factory
/// \param lifetime: Lifetime of the allocated object (AUTOMATIC_LOCAL,
///   STATIC_GLOBAL, or DYNAMIC)
/// \return Returns the symbol_exprt for the symbol created
symbol_exprt c_nondet_symbol_factory(
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &loc,
  const c_object_factory_parameterst &object_factory_parameters,
  const lifetimet lifetime)
{
  irep_idt identifier=id2string(goto_functionst::entry_point())+
    "::"+id2string(base_name);

  auxiliary_symbolt main_symbol;
  main_symbol.mode=ID_C;
  main_symbol.is_static_lifetime=false;
  main_symbol.name=identifier;
  main_symbol.base_name=base_name;
  main_symbol.type=type;
  main_symbol.location=loc;

  symbol_exprt main_symbol_expr=main_symbol.symbol_expr();

  symbolt *main_symbol_ptr;
  bool moving_symbol_failed=symbol_table.move(main_symbol, main_symbol_ptr);
  CHECK_RETURN(!moving_symbol_failed);

  symbol_factoryt state(
    symbol_table,
    loc,
    goto_functionst::entry_point(),
    object_factory_parameters,
    lifetime);

  code_blockt assignments;
  state.gen_nondet_init(assignments, main_symbol_expr);

  state.add_created_symbol(main_symbol_ptr);
  state.declare_created_symbols(init_code);

  init_code.append(assignments);

  state.mark_created_symbols_as_input(init_code);

  return main_symbol_expr;
}
