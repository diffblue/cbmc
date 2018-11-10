/*******************************************************************\

Module: Unwind loops in static initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Unwind loops in static initializers

#include "java_enum_static_init_unwind_handler.h"

#include <util/invariant.h>
#include <util/suffix.h>

/// Check if we may be in a function that loops over the cases of an
/// enumeration (note we return a candidate function that matches a pattern;
/// our caller must verify it really belongs to an enumeration).
/// At the moment we know of two cases that definitely do so:
/// * An enumeration type's static initialiser
/// * The array[reference].clone() method when called from an enumeration type's
///   'values()'  method
/// \param context: the current call stack
/// \return the name of an enclosing function that may be defined on the
///   relevant enum type, or an empty string if we don't find one.
static irep_idt
find_enum_function_on_stack(const goto_symex_statet::call_stackt &context)
{
  static irep_idt reference_array_clone_id =
    "java::array[reference].clone:()Ljava/lang/Object;";

  PRECONDITION(!context.empty());
  const irep_idt &current_function = context.back().function_identifier;

  if(context.size() >= 2 && current_function == reference_array_clone_id)
  {
    const irep_idt &clone_caller =
      context.at(context.size() - 2).function_identifier;
    if(id2string(clone_caller).find(".values:()[L") != std::string::npos)
      return clone_caller;
    else
      return irep_idt();
  }
  else if(has_suffix(id2string(current_function), ".<clinit>:()V"))
    return current_function;
  else
    return irep_idt();
}

/// Unwind handler that special-cases the clinit (static initializer) functions
/// of enumeration classes, and VALUES array cloning in their values() methods.
/// When java_bytecode_convert_classt has annotated them
/// with a size of the enumeration type, this forces unwinding of any loop in
/// the static initializer to at least that many iterations, with intent to
/// permit population / copying of the enumeration's value array.
/// \param context: call stack when the loop back-edge was taken
/// \param loop_number: ordinal number of the loop (ignored)
/// \param unwind_count: iteration count that is about to begin
/// \param [out] unwind_max: may be set to an advisory (unenforced) maximum when
///   we know the total iteration count
/// \param symbol_table: global symbol table
/// \return false if loop_id belongs to an enumeration's static initializer and
///   unwind_count is <= the enumeration size, or unknown (defer / no decision)
///   otherwise.
tvt java_enum_static_init_unwind_handler(
  const goto_symex_statet::call_stackt &context,
  unsigned loop_number,
  unsigned unwind_count,
  unsigned &unwind_max,
  const symbol_tablet &symbol_table)
{
  (void)loop_number; // unused parameter

  const irep_idt enum_function_id = find_enum_function_on_stack(context);
  if(enum_function_id.empty())
    return tvt::unknown();

  const symbolt &function_symbol = symbol_table.lookup_ref(enum_function_id);
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
