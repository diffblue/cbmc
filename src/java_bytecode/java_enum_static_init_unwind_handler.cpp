/*******************************************************************\

Module: Unwind loops in static initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Unwind loops in static initializers

#include "java_enum_static_init_unwind_handler.h"

#include <util/suffix.h>

/// Unwind handler that special-cases the clinit (static initializer) functions
/// of enumeration classes. When java_bytecode_convert_classt has annotated them
/// with a size of the enumeration type, this forces unwinding of any loop in
/// the static initializer to at least that many iterations, with intent to
/// permit population of the enumeration's value array.
/// \param function_id: function the loop is in
/// \param loop_number: ordinal number of the loop (ignored)
/// \param unwind_count: iteration count that is about to begin
/// \param [out] unwind_max: may be set to an advisory (unenforced) maximum when
///   we know the total iteration count
/// \param symbol_table: global symbol table
/// \return false if loop_id belongs to an enumeration's static initializer and
///   unwind_count is <= the enumeration size, or unknown (defer / no decision)
///   otherwise.
tvt java_enum_static_init_unwind_handler(
  const irep_idt &function_id,
  unsigned loop_number,
  unsigned unwind_count,
  unsigned &unwind_max,
  const symbol_tablet &symbol_table)
{
  const std::string &function_str = id2string(function_id);
  if(!has_suffix(function_str, ".<clinit>:()V"))
    return tvt::unknown();

  const symbolt &function_symbol = symbol_table.lookup_ref(function_str);
  irep_idt class_id = function_symbol.type.get(ID_C_class);
  INVARIANT(
    !class_id.empty(), "functions should have their defining class annotated");

  const typet &class_type = symbol_table.lookup_ref(class_id).type;
  size_t unwinds = class_type.get_size_t(ID_java_enum_static_unwind);
  if(unwinds != 0 && unwind_count < unwinds)
  {
    unwind_max = unwinds;
    return tvt(false); // Must unwind
  }
  else
  {
    return tvt::unknown(); // Defer to other unwind handlers
  }
}
