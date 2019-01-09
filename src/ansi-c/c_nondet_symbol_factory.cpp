/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#include "c_nondet_symbol_factory.h"

#include <ansi-c/c_object_factory_parameters.h>

#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/nondet_bool.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include <goto-programs/goto_functions.h>

class symbol_factoryt
{
  symbol_tablet &symbol_table;
  const source_locationt &loc;
  namespacet ns;
  const c_object_factory_parameterst &object_factory_params;

  allocate_objectst allocate_objects;

  typedef std::set<irep_idt> recursion_sett;

public:
  symbol_factoryt(
    symbol_tablet &_symbol_table,
    const source_locationt &loc,
    const c_object_factory_parameterst &object_factory_params)
    : symbol_table(_symbol_table),
      loc(loc),
      ns(_symbol_table),
      object_factory_params(object_factory_params),
      allocate_objects(ID_C, loc, loc.get_function(), symbol_table)
  {}

  /// Generate a function that behaves like malloc from our stdlib
  /// implementation
  /// \param malloc_symbol_name The name of the malloc function
  const symbolt &gen_malloc_function(const irep_idt &malloc_symbol_name);

  void gen_nondet_init(
    code_blockt &assignments,
    const exprt &expr,
    const std::size_t depth = 0,
    recursion_sett recursion_set = recursion_sett());

  void add_created_symbol(const symbolt *symbol_ptr)
  {
    allocate_objects.add_created_symbol(symbol_ptr);
  }

  void declare_created_symbols(code_blockt &init_code)
  {
    allocate_objects.declare_created_symbols(init_code);
  }

  void mark_created_symbols_as_input(code_blockt &init_code)
  {
    allocate_objects.mark_created_symbols_as_input(init_code);
  }

private:
  /// Generate initialisation code for each array element
  /// \param assignments: The code block to add code to
  /// \param expr: An expression of array type
  /// \param depth: The struct recursion depth
  /// \param recursion_set: The struct recursion set
  /// \see gen_nondet_init For the meaning of the last 2 parameters
  void gen_nondet_array_init(
    code_blockt &assignments,
    const exprt &expr,
    std::size_t depth,
    const recursion_sett &recursion_set);
};

/// Creates a nondet for expr, including calling itself recursively to make
/// appropriate symbols to point to if expr is a pointer.
/// \param assignments: The code block to add code to
/// \param expr: The expression which we are generating a non-determinate value
///   for
/// \param depth: number of pointers followed so far during initialisation
/// \param recursion_set: names of structs seen so far on current pointer chain
void symbol_factoryt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr,
  const std::size_t depth,
  recursion_sett recursion_set)
{
  const typet &type = expr.type();

  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype = pointer_type.subtype();

    if(subtype.id() == ID_struct_tag)
    {
      const irep_idt struct_tag = to_struct_tag_type(subtype).get_identifier();

      if(
        recursion_set.find(struct_tag) != recursion_set.end() &&
        depth >= object_factory_params.max_nondet_tree_depth)
      {
        assignments.add(code_assignt(expr, null_pointer_exprt(pointer_type)));

        return;
      }
    }

    code_blockt non_null_inst;

    exprt init_expr = allocate_objects.allocate_automatic_local_object(
      non_null_inst, expr, subtype);

    gen_nondet_init(non_null_inst, init_expr, depth + 1, recursion_set);

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
      auto set_null_inst=code_assignt(expr, null_pointer_exprt(pointer_type));
      set_null_inst.add_source_location()=loc;

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
      const irep_idt name = component.get_name();

      member_exprt me(expr, name, component_type);
      me.add_source_location() = loc;

      gen_nondet_init(assignments, me, depth, recursion_set);
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
    code_assignt assign(expr, rhs);
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
  auto const array_size = numeric_cast_v<size_t>(array_type.size());
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

const symbolt &
symbol_factoryt::gen_malloc_function(const irep_idt &malloc_symbol_name)
{
  // the name passed in as parameter should not exist in the symbol
  // table already
  PRECONDITION(symbol_table.lookup(malloc_symbol_name) == nullptr);

  auto source_location = source_locationt{};
  source_location.set_file(
    "<builtin-library-" + id2string(malloc_symbol_name) + ">");
  symbolt malloc_sym;
  malloc_sym.base_name = malloc_sym.name = malloc_sym.pretty_name =
    malloc_symbol_name;
  malloc_sym.mode = "C";

  auto malloc_body = code_blockt{};
  malloc_body.add_source_location() = source_location;

  // create a new local variable with this name and type, and return
  // a symbol_expr that represents this variable
  auto declare_local_variable = [&](
                                  const std::string &name, const typet &type) {
    auto const local_id = irep_idt{id2string(malloc_symbol_name) + "::" + name};
    auto local_sym = symbolt{};
    local_sym.type = type;
    local_sym.pretty_name = name;
    local_sym.name = id2string(local_id);
    local_sym.base_name = name;
    local_sym.is_lvalue = false;
    local_sym.is_static_lifetime = false;
    local_sym.is_type = false;
    local_sym.mode = "C";
    symbol_table.insert(local_sym);
    malloc_body.add(code_declt{local_sym.symbol_expr()});
    return local_sym.symbol_expr();
  };

  // declare the parameter `size_t malloc_size` for malloc
  auto malloc_size_param_symbol = symbolt{};
  malloc_size_param_symbol.type = size_type();
  malloc_size_param_symbol.name =
    id2string(malloc_symbol_name) + "::malloc_size";
  malloc_size_param_symbol.pretty_name = "malloc_size";
  malloc_size_param_symbol.base_name = "malloc_size";
  malloc_size_param_symbol.is_static_lifetime = false;
  malloc_size_param_symbol.is_parameter = true;
  symbol_table.insert(malloc_size_param_symbol);
  auto malloc_size_param = code_typet::parametert{size_type()};
  malloc_size_param.set_base_name("malloc_size");
  malloc_size_param.set_identifier(malloc_size_param_symbol.name);

  // the signature for our malloc is
  // void *__CPROVER_malloc(size_t malloc_size);
  malloc_sym.type = code_typet{code_typet::parameterst{malloc_size_param},
                               pointer_type(void_type())};

  auto const &local_size_variable = malloc_size_param_symbol.symbol_expr();

  // the variable that holds the allocation result, i.e. a valid void*
  // that points to a memory region of malloc_size bytes
  // void *malloc_res = __CPROVER_allocate(malloc_size, 0);
  auto const malloc_res =
    declare_local_variable("malloc_res", pointer_type(void_type()));

  // the actual allocation
  auto malloc_allocate = side_effect_exprt{ID_allocate};
  malloc_allocate.copy_to_operands(local_size_variable);
  malloc_allocate.copy_to_operands(false_exprt{});
  malloc_body.add(code_assignt{malloc_res, malloc_allocate});

  // the following are all setting various CBMC book-keeping variables

  // __CPROVER_deallocated=(malloc_res==__CPROVER_deallocated)?0:__CPROVER_deallocated;
  auto const &cprover_deallocated =
    symbol_table.lookup_ref(CPROVER_PREFIX "deallocated");
  malloc_body.add(code_assignt{
    cprover_deallocated.symbol_expr(),
    if_exprt{equal_exprt{malloc_res, cprover_deallocated.symbol_expr()},
             from_integer(0, cprover_deallocated.type),
             cprover_deallocated.symbol_expr()}});

  // __CPROVER_bool record_malloc=__VERIFIER_nondet___CPROVER_bool();
  auto const record_malloc =
    declare_local_variable("record_malloc", bool_typet{});
  malloc_body.add(
    code_assignt{record_malloc, get_nondet_bool(bool_typet{}, loc)});

  // __CPROVER_malloc_object=record_malloc?malloc_res:__CPROVER_malloc_object;
  auto const &malloc_object =
    symbol_table.lookup_ref(CPROVER_PREFIX "malloc_object");
  malloc_body.add(code_assignt{malloc_object.symbol_expr(),
                               if_exprt{record_malloc,
                                        malloc_res,
                                        malloc_object.symbol_expr(),
                                        malloc_object.type}});

  // __CPROVER_malloc_size=record_malloc?malloc_size:__CPROVER_malloc_size;
  auto const &malloc_size =
    symbol_table.lookup_ref(CPROVER_PREFIX "malloc_size");
  malloc_body.add(code_assignt{malloc_size.symbol_expr(),
                               if_exprt{record_malloc,
                                        local_size_variable,
                                        malloc_size.symbol_expr(),
                                        malloc_size.type}});

  // __CPROVER_malloc_is_new_array=record_malloc?0:__CPROVER_malloc_is_new_array;
  auto const &malloc_is_new_array =
    symbol_table.lookup_ref(CPROVER_PREFIX "malloc_is_new_array");
  malloc_body.add(code_assignt{
    malloc_is_new_array.symbol_expr(),
    if_exprt{record_malloc, false_exprt{}, malloc_is_new_array.symbol_expr()}});

  // __CPROVER_bool record_may_leak=__VERIFIER_nondet___CPROVER_bool();
  auto const record_may_leak =
    declare_local_variable("record_may_leak", bool_typet{});
  malloc_body.add(code_declt{record_may_leak});
  malloc_body.add(
    code_assignt{record_may_leak, get_nondet_bool(bool_typet{}, loc)});

  // __CPROVER_memory_leak=record_may_leak?malloc_res:__CPROVER_memory_leak;
  auto const &memory_leak =
    symbol_table.lookup_ref(CPROVER_PREFIX "memory_leak");
  malloc_body.add(code_assignt{
    memory_leak.symbol_expr(),
    if_exprt{record_may_leak, malloc_res, memory_leak.symbol_expr()}});

  // return malloc_res;
  malloc_body.add(code_returnt{malloc_res});

  malloc_sym.value = malloc_body;
  auto inserted_sym = symbol_table.insert(malloc_sym);

  // since the function is only called when there's no symbol with
  // malloc_sym.name already in the symbol table, inserting it does succeed
  CHECK_RETURN(inserted_sym.second);
  return inserted_sym.first;
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
/// \return Returns the symbol_exprt for the symbol created
symbol_exprt c_nondet_symbol_factory(
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &loc,
  const c_object_factory_parameterst &object_factory_parameters)
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

  symbol_factoryt state(symbol_table, loc, object_factory_parameters);
  code_blockt assignments;
  state.gen_nondet_init(assignments, main_symbol_expr);

  state.add_created_symbol(main_symbol_ptr);
  state.declare_created_symbols(init_code);

  init_code.append(assignments);

  state.mark_created_symbols_as_input(init_code);

  return main_symbol_expr;
}
