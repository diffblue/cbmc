/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#include "c_nondet_symbol_factory.h"

#include <ansi-c/c_object_factory_parameters.h>

#include <functional>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/nondet_bool.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include <goto-programs/goto_functions.h>
#include <util/array_name.h>
#include <util/optional_utils.h>
#include <util/pointer_offset_size.h>

class symbol_factoryt
{
  std::vector<const symbolt *> &symbols_created;
  symbol_tablet &symbol_table;
  const source_locationt &loc;
  namespacet ns;
  const c_object_factory_parameterst &object_factory_params;
  std::map<irep_idt, irep_idt> &deferred_array_sizes;

  typedef std::set<irep_idt> recursion_sett;

public:
  symbol_factoryt(
    std::vector<const symbolt *> &_symbols_created,
    symbol_tablet &_symbol_table,
    const source_locationt &loc,
    const c_object_factory_parameterst &object_factory_params,
    std::map<irep_idt, irep_idt> &deferred_array_sizes)
    : symbols_created(_symbols_created),
      symbol_table(_symbol_table),
      loc(loc),
      ns(_symbol_table),
      object_factory_params(object_factory_params),
      deferred_array_sizes(deferred_array_sizes)
  {}

  exprt allocate_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const bool static_lifetime);

  void gen_array_allocation(
    code_blockt &assignments,
    const exprt &array_expr,
    const exprt &size);

  /// Generate a function that behaves like malloc from our stdlib
  /// implementation
  /// \param malloc_symbol_name The name of the malloc function
  const symbolt &gen_malloc_function(const irep_idt &malloc_symbol_name);

  void gen_nondet_init(
    code_blockt &assignments,
    const exprt &expr,
    const std::size_t depth = 0,
    recursion_sett recursion_set = recursion_sett());

  void gen_nondet_array_member_initialization(
    code_blockt &assignments,
    const exprt &array,
    const exprt &array_size,
    std::size_t depth,
    const recursion_sett &recursion_set);

private:
  /// Add a new variable symbol to the symbol table
  /// \param type: The type of the new variable
  /// \param prefix: This forms the first part of the parameter,
  ///   for debugging purposes must be a valid identifier prefix
  /// \return A reference to the newly created symbol table entry
  symbolt &new_tmp_symbol(const typet &type, const std::string &prefix);
  void gen_nondet_array_init(
    code_blockt &assignments,
    const exprt &expr,
    std::size_t depth,
    const recursion_sett &recursion_set);

  using gen_array_initialization_t = std::function<void(
    code_blockt &assignments,
    const exprt &array,
    const exprt &array_size,
    std::size_t depth,
    const recursion_sett &recursion_set)>;

  /// Generate code to nondet-initialize each element of an array
  /// \param assignments: The code block the initialization statements
  ///                     are written to
  /// \param array: The expression representing the array type
  ///               (TODO: Should probably just be a plain exprt to allow
  ///                      arbitrarily nested expressions)
  /// \param depth: Struct initialisation recursion depth, \see gen_nondet_init
  /// \param recursion_set: Struct initialisation recursion set
  /// \param gen_array_initialization: A function that generates
  ///          initialisation code for array members
  void gen_nondet_size_array_init(
    code_blockt &assignments,
    const symbol_exprt &array,
    const size_t depth,
    const symbol_factoryt::recursion_sett &recursion_set,
    const gen_array_initialization_t &gen_array_initialization);

  /// Remember to initialise a variable representing array size to the given
  /// concrete size.
  /// When generating array initialisation code we often have the case where we
  /// have a pointer that should be initialised to be pointing to some array,
  /// and some integer type variable that should hold its size. Sometimes when
  /// generating the array initialisation code we haven't "seen" the size
  /// variable yet (i.e. it is not yet in the symbol table and doesn't have
  /// initialisation code generated for it yet). If that's the case we remember
  /// that we have to set it to the right size later with this method.
  /// \param associated_size_name: The of variable that should be set to
  ///         the right size
  /// \param array_size_name: The name of the variable that holds the size
  void defer_size_initialization(
    irep_idt associated_size_name,
    irep_idt array_size_name);

  /// Return the name of a variable holding an array size if one is associated
  /// with the given symbol name
  optionalt<dstringt> get_deferred_size(irep_idt symbol_name) const;

  /// Lookup symbol expression in symbol table and get its base name
  const irep_idt &get_symbol_base_name(const symbol_exprt &symbol_expr) const;
};

/// Create a symbol for a pointer to point to
/// \param assignments: The code block to add code to
/// \param target_expr: The expression which we are allocating a symbol for
/// \param allocate_type: The type to use for the symbol. If this doesn't match
///   target_expr then a cast will be used for the assignment
/// \param static_lifetime: Whether the symbol created should have static
///   lifetime
/// \return Returns the address of the allocated symbol
exprt symbol_factoryt::allocate_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  const bool static_lifetime)
{
  symbolt &aux_symbol = get_fresh_aux_symbol(
    allocate_type,
    id2string(loc.get_function()),
    "tmp",
    loc,
    ID_C,
    symbol_table);
  aux_symbol.is_static_lifetime = static_lifetime;
  symbols_created.push_back(&aux_symbol);

  const typet &allocate_type_resolved=ns.follow(allocate_type);
  const typet &target_type=ns.follow(target_expr.type().subtype());
  bool cast_needed=allocate_type_resolved!=target_type;

  exprt aoe=address_of_exprt(aux_symbol.symbol_expr());
  if(cast_needed)
  {
    aoe=typecast_exprt(aoe, target_expr.type());
  }

  // Add the following code to assignments:
  //   <target_expr> = &tmp$<temporary_counter>
  code_assignt assign(target_expr, aoe);
  assign.add_source_location()=loc;
  assignments.add(std::move(assign));

  return aoe;
}

/// Creates a nondet for expr, including calling itself recursively to make
/// appropriate symbols to point to if expr is a pointer.
/// \param assignments: The code block to add code to
/// \param expr: The expression which we are generating a non-determinate value
///   for
/// \param depth number of pointers followed so far during initialisation
/// \param recursion_set names of structs seen so far on current pointer chain
void symbol_factoryt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr,
  const std::size_t depth,
  recursion_sett recursion_set)
{
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_pointer)
  {
    if(expr.id() == ID_symbol)
    {
      auto const &symbol_expr = to_symbol_expr(expr);
      const auto &symbol_name = get_symbol_base_name(symbol_expr);
      using std::placeholders::_1;
      using std::placeholders::_2;
      using std::placeholders::_3;
      using std::placeholders::_4;
      using std::placeholders::_5;
      if(object_factory_params.should_be_treated_as_array(symbol_name))
      {
        gen_array_initialization_t gen_array_initialization = std::bind(
          &symbol_factoryt::gen_nondet_array_member_initialization,
          this,
          _1,
          _2,
          _3,
          _4,
          _5);
        gen_nondet_size_array_init(
          assignments,
          symbol_expr,
          depth,
          recursion_set,
          gen_array_initialization);
        return;
      }
    }
    // dereferenced type
    const pointer_typet &pointer_type = to_pointer_type(type);
    const typet &subtype = ns.follow(pointer_type.subtype());

    if(subtype.id() == ID_struct)
    {
      const struct_typet &struct_type = to_struct_type(subtype);
      const irep_idt struct_tag = struct_type.get_tag();

      if(
        recursion_set.find(struct_tag) != recursion_set.end() &&
        depth >= object_factory_params.max_nondet_tree_depth)
      {
        code_assignt c(expr, null_pointer_exprt(pointer_type));
        assignments.add(std::move(c));

        return;
      }
    }

    code_blockt non_null_inst;

    exprt allocated=allocate_object(non_null_inst, expr, subtype, false);

    exprt init_expr;
    if(allocated.id()==ID_address_of)
    {
      init_expr=allocated.op0();
    }
    else
    {
      init_expr=dereference_exprt(allocated, allocated.type().subtype());
    }
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

      code_ifthenelset null_check;
      null_check.cond() = side_effect_expr_nondett(bool_typet(), loc);
      null_check.then_case()=set_null_inst;
      null_check.else_case()=non_null_inst;

      assignments.add(std::move(null_check));
    }
  }
  else if(type.id() == ID_struct)
  {
    const struct_typet &struct_type = to_struct_type(type);

    const irep_idt struct_tag = struct_type.get_tag();

    recursion_set.insert(struct_tag);

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
    if(expr.id() == ID_symbol)
    {
      auto const &symbol_expr = to_symbol_expr(expr);
      auto const associated_array_size =
        get_deferred_size(get_symbol_base_name(symbol_expr));
      if(associated_array_size.has_value())
      {
        assign.rhs() = typecast_exprt{
          symbol_table.lookup_ref(associated_array_size.value()).symbol_expr(),
          symbol_expr.type()};
      }
    }
    assignments.add(std::move(assign));
  }
}

const irep_idt &
symbol_factoryt::get_symbol_base_name(const symbol_exprt &symbol_expr) const
{
  return symbol_table.lookup_ref(symbol_expr.get_identifier()).base_name;
}

void symbol_factoryt::gen_nondet_size_array_init(
  code_blockt &assignments,
  const symbol_exprt &array,
  const size_t depth,
  const symbol_factoryt::recursion_sett &recursion_set,
  const gen_array_initialization_t &gen_array_initialization)
{
  // This works on dynamic arrays, so the thing we assign to is a pointer
  // rather than an array with a fixed size
  PRECONDITION(array.type().id() == ID_pointer);

  // Overall, create code that roughly does this:
  // size_t size;
  // T *array;
  // size = choose_in_range(1, max_array_size);
  // array = malloc(sizeof(T) * size);
  // for(size_t ix = 0; ix < size; ++ix) {
  //   array[ix] = nondet_init_T();
  // }
  auto const max_array_size = object_factory_params.max_dynamic_array_size;
  auto const &array_name = get_symbol_base_name(array);
  auto const &size_symbol =
    new_tmp_symbol(size_type(), CPROVER_PREFIX "nondet_array_size");

  // assume (1 <= size && size <= max_array_size)
  auto size_initialization = code_assumet{
    and_exprt{binary_exprt{from_integer(1, size_type()),
                           ID_le,
                           size_symbol.symbol_expr(),
                           bool_typet{}},
              binary_exprt{size_symbol.symbol_expr(),
                           ID_le,
                           from_integer(max_array_size, size_type()),
                           bool_typet{}}}};

  assignments.add(size_initialization);
  gen_array_allocation(assignments, array, size_symbol.symbol_expr());
  gen_array_initialization(
    assignments, array, size_symbol.symbol_expr(), depth, recursion_set);
  // if we've already initialised the associated array size,
  // then set the associated array size to the size of the generated array
  // otherwise, defer the initialisation of the associated array size
  auto const associated_size =
    object_factory_params.get_associated_size_variable(array_name);
  if(associated_size.has_value())
  {
    auto const associated_size_symbol =
      symbol_table.lookup(associated_size.value());
    if(associated_size_symbol != nullptr)
    {
      assignments.add(
        code_assignt{associated_size_symbol->symbol_expr(),
                     typecast_exprt{size_symbol.symbol_expr(),
                                    associated_size_symbol->type}});
    }
    else
    {
      // we've not seen the associated size symbol yet, so we have
      // to defer setting it to when we do get there...
      defer_size_initialization(associated_size.value(), size_symbol.base_name);
    }
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

symbolt &
symbol_factoryt::new_tmp_symbol(const typet &type, const std::string &prefix)
{
  auto &symbol = get_fresh_aux_symbol(
    type,
    id2string(object_factory_params.function_id),
    prefix,
    loc,
    ID_C,
    symbol_table);
  symbols_created.push_back(&symbol);
  return symbol;
}

void symbol_factoryt::defer_size_initialization(
  irep_idt associated_size_name,
  irep_idt array_size_name)
{
  auto succeeded =
    deferred_array_sizes.insert({associated_size_name, array_size_name});
  INVARIANT(
    succeeded.second,
    "each size parameter should have a unique associated array");
}

optionalt<dstringt>
symbol_factoryt::get_deferred_size(irep_idt symbol_name) const
{
  return optional_lookup(deferred_array_sizes, symbol_name);
}

void symbol_factoryt::gen_array_allocation(
  code_blockt &assignments,
  const exprt &array_expr,
  const exprt &size)
{
  PRECONDITION(array_expr.type().id() == ID_pointer);
  irep_idt malloc_symbol_name = CPROVER_PREFIX "malloc";
  auto const *malloc_symbol = symbol_table.lookup(malloc_symbol_name);
  if(!malloc_symbol)
  {
    malloc_symbol = &gen_malloc_function(malloc_symbol_name);
  }
  auto const &element_type = array_expr.type().subtype();
  const exprt &array_size = size_of_expr(array_typet{element_type, size}, ns);

  // array = malloc(sizeof(array[size]))
  auto allocate_array =
    side_effect_expr_function_callt{malloc_symbol->symbol_expr(),
                                    exprt::operandst{array_size},
                                    array_expr.type(),
                                    loc};
  assignments.add(code_assignt{array_expr, allocate_array});
}

void symbol_factoryt::gen_nondet_array_member_initialization(
  code_blockt &assignments,
  const exprt &array,
  const exprt &array_size,
  std::size_t depth,
  const symbol_factoryt::recursion_sett &recursion_set)
{
  // for(size_t ix = 0; ix < size; ++ix) {
  //   arr[ix] = nondet_init_T();
  // }

  auto const &array_index_symbol = new_tmp_symbol(size_type(), "index");
  auto array_member_init = code_fort{};

  array_member_init.init() = code_assignt{array_index_symbol.symbol_expr(),
                                          from_integer(0, size_type())};

  array_member_init.cond() = binary_exprt{
    array_index_symbol.symbol_expr(), ID_lt, array_size, bool_typet{}};

  auto array_member_init_body = code_blockt{};
  gen_nondet_init(
    array_member_init_body,
    dereference_exprt{
      plus_exprt{array, array_index_symbol.symbol_expr(), array.type()}},
    depth,
    recursion_set);
  array_member_init_body.add(
    code_assignt{array_index_symbol.symbol_expr(),
                 plus_exprt{array_index_symbol.symbol_expr(),
                            from_integer(1, size_type()),
                            size_type()}});
  array_member_init.body() = std::move(array_member_init_body);
  assignments.add(std::move(array_member_init));
}

const symbolt &
symbol_factoryt::gen_malloc_function(const irep_idt &malloc_symbol_name)
{
  auto source_location = source_locationt{};
  source_location.set_file(
    "<builtin-library-" + id2string(malloc_symbol_name) + ">");
  symbolt malloc_sym;
  malloc_sym.base_name = malloc_sym.name = malloc_sym.pretty_name =
    malloc_symbol_name;
  malloc_sym.mode = "C";

  auto malloc_body = code_blockt{};
  malloc_body.add_source_location() = source_location;

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
  malloc_sym.type = code_typet{code_typet::parameterst{malloc_size_param},
                               pointer_type(void_type())};

  auto const &local_size_variable = malloc_size_param_symbol.symbol_expr();

  auto const malloc_res =
    declare_local_variable("malloc_res", pointer_type(void_type()));
  auto malloc_allocate = side_effect_exprt{ID_allocate};
  malloc_allocate.copy_to_operands(local_size_variable);
  malloc_allocate.copy_to_operands(false_exprt{});
  malloc_body.add(code_assignt{malloc_res, malloc_allocate});
  auto const &cprover_deallocated =
    symbol_table.lookup_ref(CPROVER_PREFIX "deallocated");
  malloc_body.add(code_assignt{
    cprover_deallocated.symbol_expr(),
    if_exprt{equal_exprt{malloc_res, cprover_deallocated.symbol_expr()},
             from_integer(0, cprover_deallocated.type),
             cprover_deallocated.symbol_expr()}});
  auto const record_malloc =
    declare_local_variable("record_malloc", bool_typet{});
  malloc_body.add(
    code_assignt{record_malloc, get_nondet_bool(bool_typet{}, loc)});
  auto const &malloc_object =
    symbol_table.lookup_ref(CPROVER_PREFIX "malloc_object");
  malloc_body.add(code_assignt{malloc_object.symbol_expr(),
                               if_exprt{record_malloc,
                                        malloc_res,
                                        malloc_object.symbol_expr(),
                                        malloc_object.type}});
  auto const &malloc_size =
    symbol_table.lookup_ref(CPROVER_PREFIX "malloc_size");
  malloc_body.add(code_assignt{malloc_size.symbol_expr(),
                               if_exprt{record_malloc,
                                        local_size_variable,
                                        malloc_size.symbol_expr(),
                                        malloc_size.type}});
  auto const &malloc_is_new_array =
    symbol_table.lookup_ref(CPROVER_PREFIX "malloc_is_new_array");
  malloc_body.add(code_assignt{
    malloc_is_new_array.symbol_expr(),
    if_exprt{record_malloc, false_exprt{}, malloc_is_new_array.symbol_expr()}});

  auto const record_may_leak =
    declare_local_variable("record_may_leak", bool_typet{});
  malloc_body.add(code_declt{record_may_leak});
  malloc_body.add(
    code_assignt{record_may_leak, get_nondet_bool(bool_typet{}, loc)});
  auto const &memory_leak =
    symbol_table.lookup_ref(CPROVER_PREFIX "memory_leak");
  malloc_body.add(code_assignt{
    memory_leak.symbol_expr(),
    if_exprt{record_may_leak, malloc_res, memory_leak.symbol_expr()}});
  malloc_body.add(code_returnt{malloc_res});

  malloc_sym.value = malloc_body;
  auto inserted_sym = symbol_table.insert(malloc_sym);
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
/// \param object_factory_parameters configuration parameters for the object
///   factory
/// \param deferred_array_sizes A map of size parameter name -> symbol
///        that holds the value the parameter should be assigned to
/// \return Returns the symbol_exprt for the symbol created
symbol_exprt c_nondet_symbol_factory(
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &loc,
  const c_object_factory_parameterst &object_factory_parameters,
  std::map<irep_idt, irep_idt> &deferred_array_sizes)
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

  std::vector<const symbolt *> symbols_created;
  symbols_created.push_back(main_symbol_ptr);

  symbol_factoryt state(
    symbols_created,
    symbol_table,
    loc,
    object_factory_parameters,
    deferred_array_sizes);
  code_blockt assignments;
  state.gen_nondet_init(assignments, main_symbol_expr);

  // Add the following code to init_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const symbolt * const symbol_ptr : symbols_created)
  {
    code_declt decl(symbol_ptr->symbol_expr());
    decl.add_source_location()=loc;
    init_code.add(std::move(decl));
  }

  init_code.append(assignments);

  // Add the following code to init_code for each symbol that's been created:
  //   INPUT("<identifier>", <identifier>);
  for(symbolt const *symbol_ptr : symbols_created)
  {
    codet input_code(ID_input);
    input_code.operands().resize(2);
    input_code.op0()=
      address_of_exprt(index_exprt(
        string_constantt(symbol_ptr->base_name),
        from_integer(0, index_type())));
    input_code.op1()=symbol_ptr->symbol_expr();
    input_code.add_source_location()=loc;
    init_code.add(std::move(input_code));
  }

  return main_symbol_expr;
}
