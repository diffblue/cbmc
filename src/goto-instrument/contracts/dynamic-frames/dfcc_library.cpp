/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com

\*******************************************************************/

#include "dfcc_library.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_function.h>
#include <goto-programs/goto_model.h>

#include <ansi-c/c_expr.h>
#include <ansi-c/cprover_library.h>
#include <goto-instrument/unwind.h>
#include <goto-instrument/unwindset.h>
#include <linking/static_lifetime_init.h>

#include "dfcc_utils.h"

/// Swaps keys and values in a map
template <typename K, typename V>
std::map<V, K> swap_map(std::map<K, V> const &map)
{
  std::map<V, K> result;
  for(auto const &pair : map)
    result.insert({pair.second, pair.first});
  return result;
}

// NOLINTNEXTLINE(build/deprecated)
#define CONTRACTS_PREFIX CPROVER_PREFIX "contracts_"

/// Creates the enum to type name mapping
const std::map<dfcc_typet, irep_idt> create_dfcc_type_to_name()
{
  return std::map<dfcc_typet, irep_idt>{
    {dfcc_typet::CAR, CONTRACTS_PREFIX "car_t"},
    {dfcc_typet::CAR_SET, CONTRACTS_PREFIX "car_set_t"},
    {dfcc_typet::CAR_SET_PTR, CONTRACTS_PREFIX "car_set_ptr_t"},
    {dfcc_typet::OBJ_SET, CONTRACTS_PREFIX "obj_set_t"},
    {dfcc_typet::OBJ_SET_PTR, CONTRACTS_PREFIX "obj_set_ptr_t"},
    {dfcc_typet::WRITE_SET, CONTRACTS_PREFIX "write_set_t"},
    {dfcc_typet::WRITE_SET_PTR, CONTRACTS_PREFIX "write_set_ptr_t"}};
}

const std::map<dfcc_funt, irep_idt> create_dfcc_fun_to_name()
{
  return {
    {dfcc_funt::CAR_CREATE, CONTRACTS_PREFIX "car_create"},
    {dfcc_funt::CAR_SET_CREATE, CONTRACTS_PREFIX "car_set_create"},
    {dfcc_funt::CAR_SET_INSERT, CONTRACTS_PREFIX "car_set_insert"},
    {dfcc_funt::CAR_SET_REMOVE, CONTRACTS_PREFIX "car_set_remove"},
    {dfcc_funt::CAR_SET_CONTAINS, CONTRACTS_PREFIX "car_set_contains"},
    {dfcc_funt::OBJ_SET_CREATE_INDEXED_BY_OBJECT_ID,
     CONTRACTS_PREFIX "obj_set_create_indexed_by_object_id"},
    {dfcc_funt::OBJ_SET_CREATE_APPEND,
     CONTRACTS_PREFIX "obj_set_create_append"},
    {dfcc_funt::OBJ_SET_RELEASE, CONTRACTS_PREFIX "obj_set_release"},
    {dfcc_funt::OBJ_SET_ADD, CONTRACTS_PREFIX "obj_set_add"},
    {dfcc_funt::OBJ_SET_APPEND, CONTRACTS_PREFIX "obj_set_append"},
    {dfcc_funt::OBJ_SET_REMOVE, CONTRACTS_PREFIX "obj_set_remove"},
    {dfcc_funt::OBJ_SET_CONTAINS, CONTRACTS_PREFIX "obj_set_contains"},
    {dfcc_funt::OBJ_SET_CONTAINS_EXACT,
     CONTRACTS_PREFIX "obj_set_contains_exact"},
    {dfcc_funt::WRITE_SET_CREATE, CONTRACTS_PREFIX "write_set_create"},
    {dfcc_funt::WRITE_SET_RELEASE, CONTRACTS_PREFIX "write_set_release"},
    {dfcc_funt::WRITE_SET_INSERT_ASSIGNABLE,
     CONTRACTS_PREFIX "write_set_insert_assignable"},
    {dfcc_funt::WRITE_SET_INSERT_OBJECT_WHOLE,
     CONTRACTS_PREFIX "write_set_insert_object_whole"},
    {dfcc_funt::WRITE_SET_INSERT_OBJECT_FROM,
     CONTRACTS_PREFIX "write_set_insert_object_from"},
    {dfcc_funt::WRITE_SET_INSERT_OBJECT_UPTO,
     CONTRACTS_PREFIX "write_set_insert_object_upto"},
    {dfcc_funt::WRITE_SET_ADD_FREEABLE,
     CONTRACTS_PREFIX "write_set_add_freeable"},
    {dfcc_funt::WRITE_SET_ADD_ALLOCATED,
     CONTRACTS_PREFIX "write_set_add_allocated"},
    {dfcc_funt::WRITE_SET_RECORD_DEAD,
     CONTRACTS_PREFIX "write_set_record_dead"},
    {dfcc_funt::WRITE_SET_RECORD_DEALLOCATED,
     CONTRACTS_PREFIX "write_set_record_deallocated"},
    {dfcc_funt::WRITE_SET_CHECK_ALLOCATED_DEALLOCATED_IS_EMPTY,
     CONTRACTS_PREFIX "write_set_check_allocated_deallocated_is_empty"},
    {dfcc_funt::WRITE_SET_CHECK_ASSIGNMENT,
     CONTRACTS_PREFIX "write_set_check_assignment"},
    {dfcc_funt::WRITE_SET_CHECK_ARRAY_SET,
     CONTRACTS_PREFIX "write_set_check_array_set"},
    {dfcc_funt::WRITE_SET_CHECK_ARRAY_COPY,
     CONTRACTS_PREFIX "write_set_check_array_copy"},
    {dfcc_funt::WRITE_SET_CHECK_ARRAY_REPLACE,
     CONTRACTS_PREFIX "write_set_check_array_replace"},
    {dfcc_funt::WRITE_SET_CHECK_HAVOC_OBJECT,
     CONTRACTS_PREFIX "write_set_check_havoc_object"},
    {dfcc_funt::WRITE_SET_CHECK_DEALLOCATE,
     CONTRACTS_PREFIX "write_set_check_deallocate"},
    {dfcc_funt::WRITE_SET_CHECK_ASSIGNS_CLAUSE_INCLUSION,
     CONTRACTS_PREFIX "write_set_check_assigns_clause_inclusion"},
    {dfcc_funt::WRITE_SET_CHECK_FREES_CLAUSE_INCLUSION,
     CONTRACTS_PREFIX "write_set_check_frees_clause_inclusion"},
    {dfcc_funt::WRITE_SET_DEALLOCATE_FREEABLE,
     CONTRACTS_PREFIX "write_set_deallocate_freeable"},
    {dfcc_funt::WRITE_SET_HAVOC_GET_ASSIGNABLE_TARGET,
     CONTRACTS_PREFIX "write_set_havoc_get_assignable_target"},
    {dfcc_funt::WRITE_SET_HAVOC_OBJECT_WHOLE,
     CONTRACTS_PREFIX "write_set_havoc_object_whole"},
    {dfcc_funt::WRITE_SET_HAVOC_SLICE,
     CONTRACTS_PREFIX "write_set_havoc_slice"},
    {dfcc_funt::LINK_IS_FRESH, CONTRACTS_PREFIX "link_is_fresh"},
    {dfcc_funt::LINK_ALLOCATED, CONTRACTS_PREFIX "link_allocated"},
    {dfcc_funt::LINK_DEALLOCATED, CONTRACTS_PREFIX "link_deallocated"},
    {dfcc_funt::IS_FRESH, CONTRACTS_PREFIX "is_fresh"},
    {dfcc_funt::IS_FREEABLE, CONTRACTS_PREFIX "is_freeable"},
    {dfcc_funt::WAS_FREED, CONTRACTS_PREFIX "was_freed"},
    {dfcc_funt::REPLACE_ENSURES_WAS_FREED_PRECONDITIONS,
     CONTRACTS_PREFIX "check_replace_ensures_was_freed_preconditions"}};
}

const std::map<irep_idt, dfcc_funt> create_dfcc_hook()
{
  return {
    {CPROVER_PREFIX "assignable", dfcc_funt::WRITE_SET_INSERT_ASSIGNABLE},
    {CPROVER_PREFIX "object_whole", dfcc_funt::WRITE_SET_INSERT_OBJECT_WHOLE},
    {CPROVER_PREFIX "object_from", dfcc_funt::WRITE_SET_INSERT_OBJECT_FROM},
    {CPROVER_PREFIX "object_upto", dfcc_funt::WRITE_SET_INSERT_OBJECT_UPTO},
    {CPROVER_PREFIX "freeable", dfcc_funt::WRITE_SET_ADD_FREEABLE}};
}

const std::map<irep_idt, dfcc_funt> create_havoc_hook()
{
  return {
    {CPROVER_PREFIX "assignable",
     dfcc_funt::WRITE_SET_HAVOC_GET_ASSIGNABLE_TARGET},
    {CPROVER_PREFIX "object_whole", dfcc_funt::WRITE_SET_HAVOC_OBJECT_WHOLE},
    {CPROVER_PREFIX "object_from", dfcc_funt::WRITE_SET_HAVOC_SLICE},
    {CPROVER_PREFIX "object_upto", dfcc_funt::WRITE_SET_HAVOC_SLICE}};
}

const std::set<irep_idt> create_assignable_builtin_names()
{
  return {
    CPROVER_PREFIX "assignable",
    CPROVER_PREFIX "assignable_set_insert_assignable",
    CPROVER_PREFIX "object_whole",
    CPROVER_PREFIX "assignable_set_insert_object_whole",
    CPROVER_PREFIX "object_from",
    CPROVER_PREFIX "assignable_set_insert_object_from",
    CPROVER_PREFIX "object_upto",
    CPROVER_PREFIX "assignable_set_insert_object_upto",
    CPROVER_PREFIX "freeable",
    CPROVER_PREFIX "assignable_set_add_freeable"};
}

/// Class constructor
dfcc_libraryt::dfcc_libraryt(
  goto_modelt &goto_model,
  dfcc_utilst &utils,
  message_handlert &message_handler)
  : goto_model(goto_model),
    utils(utils),
    message_handler(message_handler),
    log(message_handler),
    dfcc_type_to_name(create_dfcc_type_to_name()),
    dfcc_name_to_type(swap_map<dfcc_typet, irep_idt>(dfcc_type_to_name)),
    dfcc_fun_to_name(create_dfcc_fun_to_name()),
    dfcc_name_to_fun(swap_map<dfcc_funt, irep_idt>(dfcc_fun_to_name)),
    dfcc_hook(create_dfcc_hook()),
    havoc_hook(create_havoc_hook()),
    assignable_builtin_names(create_assignable_builtin_names())
{
  // Add the instrumented map symbol to the symbol table.
  get_instrumented_functions_map_symbol();
}

/// Returns the instrumentation function to use for a given front-end function
bool dfcc_libraryt::is_front_end_builtin(const irep_idt &function_id) const
{
  return dfcc_hook.find(function_id) != dfcc_hook.end();
}

/// Returns the instrumentation function to use for a given front-end function
dfcc_funt dfcc_libraryt::get_hook(const irep_idt &function_id) const
{
  PRECONDITION(is_front_end_builtin(function_id));
  return dfcc_hook.find(function_id)->second;
}

// Returns the havoc function to use for a given front-end function
optionalt<dfcc_funt>
dfcc_libraryt::get_havoc_hook(const irep_idt &function_id) const
{
  auto found = havoc_hook.find(function_id);
  if(found != havoc_hook.end())
    return {found->second};
  else
    return {};
}

std::set<irep_idt> dfcc_libraryt::get_missing_funs()
{
  std::set<irep_idt> missing;

  // add `malloc` since it is needed used by the `is_fresh` function
  missing.insert("malloc");

  // add `free` and `__CPROVER_deallocate` since they are used by the
  // `write_set_deallocate_freeable`
  missing.insert("free");

  // used by `write_set_release`
  missing.insert(CPROVER_PREFIX "deallocate");

  // Make sure all front end functions are loaded
  missing.insert(CPROVER_PREFIX "assignable");
  missing.insert(CPROVER_PREFIX "object_from");
  missing.insert(CPROVER_PREFIX "object_upto");
  missing.insert(CPROVER_PREFIX "object_whole");
  missing.insert(CPROVER_PREFIX "freeable");

  // go over all library functions
  for(const auto &pair : dfcc_fun_to_name)
  {
    symbol_tablet::symbolst::const_iterator found =
      goto_model.symbol_table.symbols.find(pair.second);

    if(
      found == goto_model.symbol_table.symbols.end() ||
      found->second.value.is_nil())
    {
      missing.insert(pair.second);
    }
  }
  return missing;
}

bool dfcc_libraryt::loaded = false;

void dfcc_libraryt::load(std::set<irep_idt> &to_instrument)
{
  PRECONDITION_WITH_DIAGNOSTICS(
    !loaded, "the cprover_contracts library can only be loaded once");
  loaded = true;

  log.status() << "Adding the cprover_contracts library (" << config.ansi_c.arch
               << ")" << messaget::eom;

  // these will need to get instrumented as well
  to_instrument.insert("malloc");
  to_instrument.insert("free");
  to_instrument.insert(CPROVER_PREFIX "deallocate");

  std::set<irep_idt> to_load;

  // add the whole library
  to_load.insert(CPROVER_PREFIX "contracts_library");

  // add front end functions
  to_load.insert(CPROVER_PREFIX "assignable");
  to_load.insert(CPROVER_PREFIX "object_from");
  to_load.insert(CPROVER_PREFIX "object_upto");
  to_load.insert(CPROVER_PREFIX "object_whole");
  to_load.insert(CPROVER_PREFIX "freeable");

  // add stdlib dependences
  to_load.insert("malloc");
  to_load.insert("free");
  to_load.insert(CPROVER_PREFIX "deallocate");

  symbol_tablet tmp_symbol_table;
  cprover_c_library_factory_force_load(
    to_load, tmp_symbol_table, message_handler);

  // compute missing library functions before modifying the symbol table
  std::set<irep_idt> missing = get_missing_funs();

  // copy all loaded symbols to the main symbol table
  for(const auto &symbol_pair : tmp_symbol_table.symbols)
  {
    const auto &sym = symbol_pair.first;
    if(!goto_model.symbol_table.has_symbol(sym))
      goto_model.symbol_table.insert(symbol_pair.second);
  }

  // compile all missing library functions to GOTO
  for(const auto &id : missing)
  {
    goto_convert(
      id, goto_model.symbol_table, goto_model.goto_functions, message_handler);
  }

  // check that all symbols have a goto_implementation
  // and populate symbol maps
  namespacet ns(goto_model.symbol_table);
  for(const auto &pair : dfcc_fun_to_name)
  {
    const auto &found =
      goto_model.goto_functions.function_map.find(pair.second);

    INVARIANT(
      found != goto_model.goto_functions.function_map.end() &&
        found->second.body_available(),
      "The body of DFCC library function " + id2string(pair.second) +
        " could not be found");

    dfcc_fun_symbol[pair.first] = ns.lookup(pair.second);
  }

  // populate symbol maps for easy access to symbols during translation
  for(const auto &pair : dfcc_type_to_name)
  {
    dfcc_type[pair.first] = ns.lookup(pair.second).type;
  }

  // fix malloc and free calls
  fix_malloc_free_calls();

  // inline the functions that need to be inlined for perf reasons
  inline_functions();

  // hide all instructions in counter example traces
  set_hide(true);
}

optionalt<dfcc_funt> dfcc_libraryt::get_dfcc_fun(const irep_idt &id) const
{
  auto found = dfcc_name_to_fun.find(id);
  if(found != dfcc_name_to_fun.end())
    return {found->second};
  else
    return {};
}

bool dfcc_libraryt::is_dfcc_library_symbol(const irep_idt &id) const
{
  return get_dfcc_fun(id).has_value();
}

const irep_idt &dfcc_libraryt::get_dfcc_fun_name(dfcc_funt fun) const
{
  return dfcc_fun_to_name.at(fun);
}

/// set of functions that need to be inlined
static const std::set<dfcc_funt> to_inline = {
  dfcc_funt::WRITE_SET_CREATE,
  dfcc_funt::WRITE_SET_RELEASE,
  dfcc_funt::WRITE_SET_INSERT_ASSIGNABLE,
  dfcc_funt::WRITE_SET_INSERT_OBJECT_WHOLE,
  dfcc_funt::WRITE_SET_INSERT_OBJECT_FROM,
  dfcc_funt::WRITE_SET_INSERT_OBJECT_UPTO,
  dfcc_funt::WRITE_SET_ADD_FREEABLE,
  dfcc_funt::WRITE_SET_ADD_ALLOCATED,
  dfcc_funt::WRITE_SET_RECORD_DEAD,
  dfcc_funt::WRITE_SET_RECORD_DEALLOCATED,
  dfcc_funt::WRITE_SET_CHECK_ASSIGNMENT,
  dfcc_funt::WRITE_SET_CHECK_ARRAY_SET,
  dfcc_funt::WRITE_SET_CHECK_ARRAY_COPY,
  dfcc_funt::WRITE_SET_CHECK_ARRAY_REPLACE,
  dfcc_funt::WRITE_SET_CHECK_HAVOC_OBJECT,
  dfcc_funt::WRITE_SET_CHECK_DEALLOCATE,
  dfcc_funt::WRITE_SET_DEALLOCATE_FREEABLE};

bool dfcc_libraryt::inlined = false;

void dfcc_libraryt::inline_functions()
{
  INVARIANT(!inlined, "inline_functions can only be called once");
  inlined = true;
  for(const auto &function_id : to_inline)
  {
    utils.inline_function(dfcc_fun_to_name.at(function_id));
  }
}

/// set of functions that need to be unwound to assigns clause size with
/// corresponding loop identifiers.
static const std::map<dfcc_funt, int> to_unwind = {
  {dfcc_funt::WRITE_SET_CHECK_ASSIGNMENT, 0},
  {dfcc_funt::WRITE_SET_CHECK_ARRAY_SET, 0},
  {dfcc_funt::WRITE_SET_CHECK_ARRAY_COPY, 0},
  {dfcc_funt::WRITE_SET_CHECK_ARRAY_REPLACE, 0},
  {dfcc_funt::WRITE_SET_CHECK_HAVOC_OBJECT, 0},
  {dfcc_funt::WRITE_SET_RECORD_DEALLOCATED, 0}};

bool dfcc_libraryt::specialized = false;

void dfcc_libraryt::specialize(const std::size_t contract_assigns_size)
{
  INVARIANT(
    !specialized,
    "dfcc_libraryt::specialize_functions can only be called once");

  specialized = true;
  unwindsett unwindset{goto_model};
  std::list<std::string> loop_names;

  for(const auto &entry : to_unwind)
  {
    const auto &function = entry.first;
    const auto &loop_id = entry.second;
    std::stringstream stream;
    stream << id2string(dfcc_fun_to_name.at(function)) << "." << loop_id << ":"
           << contract_assigns_size + 1;
    const auto &str = stream.str();
    loop_names.push_back(str);
  }
  unwindset.parse_unwindset(loop_names, message_handler);
  goto_unwindt goto_unwind;
  goto_unwind(
    goto_model, unwindset, goto_unwindt::unwind_strategyt::ASSERT_ASSUME);
}

/// Set of functions that contain calls to assignable_malloc or assignable_free
static const std::set<dfcc_funt> fix_malloc_free_set = {
  dfcc_funt::WRITE_SET_DEALLOCATE_FREEABLE,
  dfcc_funt::IS_FRESH};

/// True iff the library functions have already been fixed
bool dfcc_libraryt::malloc_free_fixed = false;

void dfcc_libraryt::fix_malloc_free_calls()
{
  INVARIANT(
    !malloc_free_fixed,
    "dfcc_libraryt::fix_malloc_free_calls can only be called once");
  malloc_free_fixed = true;
  for(const auto fun : fix_malloc_free_set)
  {
    goto_programt &prog =
      goto_model.goto_functions.function_map.at(dfcc_fun_to_name.at(fun)).body;

    Forall_goto_program_instructions(ins, prog)
    {
      if(ins->is_function_call())
      {
        const auto &function = ins->call_function();

        if(function.id() == ID_symbol)
        {
          const irep_idt &fun_name = to_symbol_expr(function).get_identifier();

          if(fun_name == (CONTRACTS_PREFIX "malloc"))
            to_symbol_expr(ins->call_function()).set_identifier("malloc");

          if(fun_name == (CONTRACTS_PREFIX "free"))
            to_symbol_expr(ins->call_function()).set_identifier("free");
        }
      }
    }
  }
}

void dfcc_libraryt::inhibit_front_end_builtins()
{
  for(const auto &it : dfcc_hook)
  {
    const auto &fid = it.first;
    if(goto_model.symbol_table.has_symbol(fid))
    {
      // make sure parameter symbols exist
      utils.fix_parameters_symbols(fid);

      // create fatal assertion code block as body
      source_locationt sl;
      sl.set_function(fid);
      sl.set_file("<built-in-additions>");
      sl.set_property_class("sanity_check");
      sl.set_comment(
        "Built-in " + id2string(fid) +
        " should not be called after contracts transformation");
      auto block = create_fatal_assertion(false_exprt(), sl);
      auto &symbol = goto_model.symbol_table.get_writeable_ref(fid);
      symbol.value = block;

      // convert the function
      goto_convert(
        fid,
        goto_model.symbol_table,
        goto_model.goto_functions,
        message_handler);
    }
  }
}

/// Sets the given hide flag on all instructions of all library functions
void dfcc_libraryt::set_hide(bool hide)
{
  PRECONDITION(dfcc_libraryt::loaded);
  for(auto it : dfcc_fun_symbol)
    utils.set_hide(it.second.name, hide);
}

const symbolt &dfcc_libraryt::get_instrumented_functions_map_symbol()
{
  const irep_idt map_name = "__dfcc_instrumented_functions";

  if(goto_model.symbol_table.has_symbol(map_name))
    return goto_model.symbol_table.lookup_ref(map_name);

  auto map_type =
    array_typet(unsigned_char_type(), infinity_exprt(size_type()));

  return utils.create_static_symbol(
    map_type,
    "",
    "__dfcc_instrumented_functions",
    source_locationt{},
    ID_C,
    "<built-in-library>",
    array_of_exprt(from_integer(0, map_type.element_type()), map_type),
    true);
}

void dfcc_libraryt::add_instrumented_functions_map_init_instructions(
  const std::set<irep_idt> &instrumented_functions,
  const source_locationt &source_location,
  goto_programt &dest)
{
  auto instrumented_functions_map =
    get_instrumented_functions_map_symbol().symbol_expr();

  for(auto &function_id : instrumented_functions)
  {
    auto object_id = pointer_object(
      address_of_exprt(utils.get_function_symbol(function_id).symbol_expr()));
    auto index_expr = index_exprt(instrumented_functions_map, object_id);
    dest.add(goto_programt::make_assignment(
      index_expr, from_integer(1, unsigned_char_type()), source_location));
  }
  goto_model.goto_functions.update();
}
