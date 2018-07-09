/*******************************************************************\

Module: Unwind loops in array clone for enums

Author: Diffblue

\*******************************************************************/

/// \file
/// Unwind loops in array.clone for enums
#include "java_enum_array_clone_unwind_handler.h"

#include <util/invariant.h>
#include <util/suffix.h>

#include <java_bytecode/java_utils.h>

/// Unwind handler that specializes the clone functions of arrays of enumeration
/// classes.  This forces unwinding of the copy loop in the clone method with as
/// many iterations as enum elements exist.
/// \param function_id: function the loop is in
/// \param loop_number: ordinal number of the loop (ignored)
/// \param unwind_count: iteration count that is about to begin
/// \param [out] unwind_max: may be set to an advisory (unenforced) maximum when
/// we know the total iteration count
/// \param symbol_table: global symbol table
/// \return false if loop_id belongs to an enumeration's array clone method and
/// unwind_count is <= the enumeration size, or unknown (defer / no decision)
/// otherwise.
tvt java_enum_array_clone_unwind_handler(
  const irep_idt &function_id,
  unsigned loop_number,
  unsigned unwind_count,
  unsigned &unwind_max,
  const symbol_tablet &symbol_table)
{
  const std::string method_name = id2string(function_id);
  const std::string java_array_prefix = "java::array[";
  const size_t java_array_prefix_start = method_name.find(java_array_prefix);
  const size_t java_array_prefix_end =
    method_name.find("].clone:()Ljava/lang/Object;");
  if(java_array_prefix_end == std::string::npos || java_array_prefix_start != 0)
    return tvt::unknown();

  const java_enum_elements_mapt java_enum_elements =
    get_java_enum_elements_map(symbol_table);

  std::string enum_name = "java::" +
                          method_name.substr(
                            java_array_prefix.size(),
                            java_array_prefix_end - java_array_prefix.size());
  std::replace(enum_name.begin(), enum_name.end(), '/', '.');
  const auto entry = java_enum_elements.find(enum_name);

  if(entry != java_enum_elements.end())
  {
    const size_t bound = entry->second;
    if(unwind_count < bound)
    {
      unwind_max = bound;
      return tvt(false);
    }
  }
  return tvt::unknown();
}
