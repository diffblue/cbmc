/*******************************************************************\

Module: Java Static Initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "java_static_initializers.h"
#include <goto-programs/class_hierarchy.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/suffix.h>

// Disable linter here to allow a std::string constant, since that holds
// a length, whereas a cstr would require strlen every time.
const std::string clinit_wrapper_suffix = "::clinit_wrapper"; // NOLINT(*)

/// Get the Java static initializer wrapper name for a given class (the wrapper
/// checks if static initialization has already been done before invoking the
/// real static initializer if not).
/// Doesn't check whether the symbol actually exists
/// \param class_name: class symbol name
/// \return static initializer wrapper name
irep_idt clinit_wrapper_name(const irep_idt &class_name)
{
  return id2string(class_name) + clinit_wrapper_suffix;
}

/// Get the class name from a clinit wrapper name. This is the opposite of
/// `clinit_wrapper_name`.
/// \param wrapper_name: clinit wrapper name
/// \return class name
static irep_idt clinit_wrapper_name_to_class_name(const irep_idt &wrapper_name)
{
  const std::string &wrapper_str = id2string(wrapper_name);
  PRECONDITION(wrapper_str.size() > clinit_wrapper_suffix.size());
  return wrapper_str.substr(
    0, wrapper_str.size() - clinit_wrapper_suffix.size());
}

/// Check if function_id is a clinit wrapper
/// \param function_id: some function identifier
/// \return true if the passed identifier is a clinit wrapper
bool is_clinit_wrapper_function(const irep_idt &function_id)
{
  return has_suffix(id2string(function_id), clinit_wrapper_suffix);
}

/// Get name of the static-initialization-already-done global variable for a
/// given class.
/// \param class_name: class symbol name
/// \return static initializer wrapper-already run global name
static irep_idt clinit_already_run_variable_name(const irep_idt &class_name)
{
  return id2string(class_name) + "::clinit_already_run";
}

/// Get name of the real static initializer for a given class. Doesn't check
/// if a static initializer actually exists.
/// \param class_name: class symbol name
/// \return Static initializer symbol name
static irep_idt clinit_function_name(const irep_idt &class_name)
{
  return id2string(class_name) + ".<clinit>:()V";
}

/// Checks whether a static initializer wrapper is needed for a given class,
/// i.e. if the given class or any superclass has a static initializer.
/// \param class_name: class symbol name
/// \param symbol_table: global symbol table
/// \return true if a static initializer wrapper is needed
static bool needs_clinit_wrapper(
  const irep_idt &class_name, const symbol_tablet &symbol_table)
{
  if(symbol_table.has_symbol(clinit_function_name(class_name)))
    return true;

  const class_typet &class_type =
    to_class_type(symbol_table.lookup_ref(class_name).type);

  for(const class_typet::baset &base : class_type.bases())
  {
    if(symbol_table.has_symbol(
         clinit_wrapper_name(to_symbol_type(base.type()).get_identifier())))
    {
      return true;
    }
  }

  return false;
}

/// Creates a static initializer wrapper symbol for the given class, along with
/// a global boolean that tracks if it has been run already.
/// \param class_name: class symbol name
/// \param symbol_table: global symbol table; will gain a clinit_wrapper symbol
///   and a corresponding has-run-already global.
static void create_clinit_wrapper_symbols(
  const irep_idt &class_name, symbol_tablet &symbol_table)
{
  const irep_idt &already_run_name =
    clinit_already_run_variable_name(class_name);
  symbolt already_run_symbol;
  already_run_symbol.name = already_run_name;
  already_run_symbol.pretty_name = already_run_name;
  already_run_symbol.base_name = "clinit_already_run";
  already_run_symbol.type = bool_typet();
  already_run_symbol.value = false_exprt();
  already_run_symbol.is_lvalue = true;
  already_run_symbol.is_state_var = true;
  already_run_symbol.is_static_lifetime = true;
  already_run_symbol.mode = ID_java;
  bool failed = symbol_table.add(already_run_symbol);
  INVARIANT(!failed, "clinit-already-run symbol should be fresh");

  symbolt wrapper_method_symbol;
  code_typet wrapper_method_type;
  wrapper_method_type.return_type() = void_typet();
  wrapper_method_symbol.name = clinit_wrapper_name(class_name);
  wrapper_method_symbol.pretty_name = wrapper_method_symbol.name;
  wrapper_method_symbol.base_name = "clinit_wrapper";
  wrapper_method_symbol.type = wrapper_method_type;
  wrapper_method_symbol.mode = ID_java;
  failed = symbol_table.add(wrapper_method_symbol);
  INVARIANT(!failed, "clinit-wrapper symbol should be fresh");
}

/// Produces the static initialiser wrapper body for the given function.
/// \param function_id: clinit wrapper function id (the wrapper_method_symbol
///   name created by `create_clinit_wrapper_symbols`)
/// \param symbol_table: global symbol table
/// \return the body of the static initialiser wrapper
codet get_clinit_wrapper_body(
  const irep_idt &function_id, const symbol_tablet &symbol_table)
{
  // Assume that class C extends class C' and implements interfaces
  // I1, ..., In. We now create the following function (possibly recursively
  // creating the clinit_wrapper functions for C' and I1, ..., In):
  //
  // java::C::clinit_wrapper()
  // {
  //   if (java::C::clinit_already_run == false)
  //   {
  //     java::C::clinit_already_run = true; // before recursive calls!
  //
  //     java::C'::clinit_wrapper();
  //     java::I1::clinit_wrapper();
  //     java::I2::clinit_wrapper();
  //     // ...
  //     java::In::clinit_wrapper();
  //
  //     java::C::<clinit>();
  //   }
  // }
  irep_idt class_name = clinit_wrapper_name_to_class_name(function_id);
  const symbolt &already_run_symbol =
    symbol_table.lookup_ref(clinit_already_run_variable_name(class_name));

  equal_exprt check_already_run(
    already_run_symbol.symbol_expr(),
    false_exprt());

  // the entire body of the function is an if-then-else
  code_ifthenelset wrapper_body;

  // add the condition to the if
  wrapper_body.cond()=check_already_run;

  // add the "already-run = false" statement
  code_blockt init_body;
  code_assignt set_already_run(already_run_symbol.symbol_expr(), true_exprt());
  init_body.move_to_operands(set_already_run);

  // iterate through the base types and add recursive calls to the
  // clinit_wrapper()
  const symbolt &class_symbol = symbol_table.lookup_ref(class_name);
  for(const auto &base : to_class_type(class_symbol.type).bases())
  {
    const auto base_name = to_symbol_type(base.type()).get_identifier();
    irep_idt base_init_routine = clinit_wrapper_name(base_name);
    auto findit = symbol_table.symbols.find(base_init_routine);
    if(findit == symbol_table.symbols.end())
      continue;
    code_function_callt call_base;
    call_base.function() = findit->second.symbol_expr();
    init_body.move_to_operands(call_base);
  }

  // call java::C::<clinit>(), if the class has one static initializer
  const irep_idt &real_clinit_name = clinit_function_name(class_name);
  auto find_sym_it = symbol_table.symbols.find(real_clinit_name);
  if(find_sym_it!=symbol_table.symbols.end())
  {
    code_function_callt call_real_init;
    call_real_init.function()=find_sym_it->second.symbol_expr();
    init_body.move_to_operands(call_real_init);
  }
  wrapper_body.then_case()=init_body;

  return wrapper_body;
}

/// Create static initializer wrappers for all classes that need them.
/// \param symbol_table: global symbol table
void create_static_initializer_wrappers(symbol_tablet &symbol_table)
{
  // Top-sort the class hierarchy, such that we visit parents before children,
  // and can so identify parents that need static initialisation by whether we
  // have made them a clinit_wrapper method.
  class_hierarchy_grapht class_graph;
  class_graph.populate(symbol_table);
  std::list<class_hierarchy_grapht::node_indext> topsorted_nodes =
    class_graph.topsort();

  for(const auto node : topsorted_nodes)
  {
    const irep_idt &class_identifier = class_graph[node].class_identifier;
    if(needs_clinit_wrapper(class_identifier, symbol_table))
      create_clinit_wrapper_symbols(class_identifier, symbol_table);
  }
}
