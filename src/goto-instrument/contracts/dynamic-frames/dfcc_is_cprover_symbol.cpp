/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_is_cprover_symbol.h"

#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/suffix.h>

#include <unordered_set>

static void
init_function_symbols(std::unordered_set<irep_idt> &function_symbols)
{
  // the set of all CPROVER symbols that we know of
  if(function_symbols.empty())
  {
    function_symbols.insert(CPROVER_PREFIX "_start");
    function_symbols.insert(CPROVER_PREFIX "allocated_memory");
    function_symbols.insert(CPROVER_PREFIX "array_copy");
    function_symbols.insert(CPROVER_PREFIX "array_replace");
    function_symbols.insert(CPROVER_PREFIX "array_set");
    function_symbols.insert(CPROVER_PREFIX "assert");
    function_symbols.insert(CPROVER_PREFIX "assignable");
    function_symbols.insert(CPROVER_PREFIX "assume");
    function_symbols.insert(CPROVER_PREFIX "contracts_car_create");
    function_symbols.insert(CPROVER_PREFIX "contracts_car_set_contains");
    function_symbols.insert(CPROVER_PREFIX "contracts_car_set_create");
    function_symbols.insert(CPROVER_PREFIX "contracts_car_set_insert");
    function_symbols.insert(CPROVER_PREFIX "contracts_car_set_remove");
    function_symbols.insert(
      CPROVER_PREFIX "contracts_check_replace_ensures_was_freed_preconditions");
    function_symbols.insert(CPROVER_PREFIX "contracts_free");
    function_symbols.insert(CPROVER_PREFIX "contracts_is_freeable");
    function_symbols.insert(CPROVER_PREFIX "contracts_is_fresh");
    function_symbols.insert(CPROVER_PREFIX "contracts_link_allocated");
    function_symbols.insert(CPROVER_PREFIX "contracts_link_deallocated");
    function_symbols.insert(CPROVER_PREFIX "contracts_link_is_fresh");
    function_symbols.insert(CPROVER_PREFIX "contracts_obeys_contract");
    function_symbols.insert(CPROVER_PREFIX "contracts_obj_set_add");
    function_symbols.insert(CPROVER_PREFIX "contracts_obj_set_append");
    function_symbols.insert(CPROVER_PREFIX "contracts_obj_set_contains_exact");
    function_symbols.insert(CPROVER_PREFIX "contracts_obj_set_contains");
    function_symbols.insert(CPROVER_PREFIX "contracts_obj_set_create_append");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_obj_set_create_indexed_by_object_id");
    function_symbols.insert(CPROVER_PREFIX "contracts_obj_set_release");
    function_symbols.insert(CPROVER_PREFIX "contracts_obj_set_remove");
    function_symbols.insert(CPROVER_PREFIX "contracts_pointer_in_range_dfcc");
    function_symbols.insert(CPROVER_PREFIX "contracts_was_freed");
    function_symbols.insert(CPROVER_PREFIX "contracts_write_set_add_allocated");
    function_symbols.insert(CPROVER_PREFIX "contracts_write_set_add_decl");
    function_symbols.insert(CPROVER_PREFIX "contracts_write_set_add_freeable");
    function_symbols.insert(
      CPROVER_PREFIX
      "contracts_write_set_check_allocated_deallocated_is_empty");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_check_array_copy");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_check_array_replace");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_check_array_set");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_check_assignment");
    function_symbols.insert(
      CPROVER_PREFIX "contracts_write_set_check_assigns_clause_inclusion");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_check_deallocate");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_check_frees_clause_inclusion");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_check_havoc_object");
    function_symbols.insert(CPROVER_PREFIX "contracts_write_set_create");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_deallocate_freeable");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_havoc_get_assignable_target");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_havoc_object_whole");
    function_symbols.insert(CPROVER_PREFIX "contracts_write_set_havoc_slice");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_insert_assignable");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_insert_object_from");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_insert_object_upto");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_insert_object_whole");
    function_symbols.insert(CPROVER_PREFIX "contracts_write_set_record_dead");
    function_symbols.insert(CPROVER_PREFIX
                            "contracts_write_set_record_deallocated");
    function_symbols.insert(CPROVER_PREFIX "contracts_write_set_release");
    function_symbols.insert(CPROVER_PREFIX "deallocate");
    function_symbols.insert(CPROVER_PREFIX "freeable");
    function_symbols.insert(CPROVER_PREFIX "havoc_object");
    function_symbols.insert(CPROVER_PREFIX "havoc_slice");
    function_symbols.insert(CPROVER_PREFIX "initialize");
    function_symbols.insert(CPROVER_PREFIX "is_freeable");
    function_symbols.insert(CPROVER_PREFIX "is_fresh");
    function_symbols.insert(CPROVER_PREFIX "obeys_contract");
    function_symbols.insert(CPROVER_PREFIX "object_from");
    function_symbols.insert(CPROVER_PREFIX "object_upto");
    function_symbols.insert(CPROVER_PREFIX "object_whole");
    function_symbols.insert(CPROVER_PREFIX "pointer_in_range_dfcc");
    function_symbols.insert(CPROVER_PREFIX "precondition");
    function_symbols.insert(CPROVER_PREFIX "printf");
    function_symbols.insert(CPROVER_PREFIX "was_freed");
  }
}

static void init_static_symbols(std::unordered_set<irep_idt> &static_symbols)
{
  if(static_symbols.empty())
  {
    static_symbols.insert(CPROVER_PREFIX "dead_object");
    static_symbols.insert(CPROVER_PREFIX "deallocated");
    static_symbols.insert(CPROVER_PREFIX "fpu_control_word");
    static_symbols.insert(CPROVER_PREFIX "jsa_jump_buffer");
    static_symbols.insert(CPROVER_PREFIX "malloc_failure_mode_return_null");
    static_symbols.insert(CPROVER_PREFIX
                          "malloc_failure_mode_assert_then_assume");
    static_symbols.insert(CPROVER_PREFIX "malloc_is_new_array");
    static_symbols.insert(CPROVER_PREFIX "max_malloc_size");
    static_symbols.insert(CPROVER_PREFIX "memory_leak");
    static_symbols.insert(CPROVER_PREFIX "pipe_offset");
    static_symbols.insert(CPROVER_PREFIX "pipes");
    static_symbols.insert(CPROVER_PREFIX "rounding_mode");
  }
}

bool dfcc_is_cprover_function_symbol(const irep_idt &id)
{
  std::unordered_set<irep_idt> function_symbols;
  init_function_symbols(function_symbols);
  std::string str = id2string(id);
  return function_symbols.find(id) != function_symbols.end() ||
         // nondet functions
         has_prefix(str, "__VERIFIER") || has_prefix(str, "nondet");
}

bool dfcc_is_cprover_static_symbol(const irep_idt &id)
{
  std::unordered_set<irep_idt> static_symbols;
  init_static_symbols(static_symbols);
  return static_symbols.find(id) != static_symbols.end() ||
         // auto objects from pointer derefs
         has_suffix(id2string(id), "$object") ||
         // going_to variables converted from goto statements
         has_prefix(id2string(id), CPROVER_PREFIX "going_to");
}
