/*******************************************************************\

Module: Simple Java method stubbing

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Java simple opaque stub generation

#include "simple_method_stubbing.h"

#include <java_bytecode/java_object_factory.h>
#include <java_bytecode/java_pointer_casts.h>

#include <util/fresh_symbol.h>
#include <util/invariant_utils.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>

class java_simple_method_stubst
{
public:
  java_simple_method_stubst(
    symbol_table_baset &_symbol_table,
    bool _assume_non_null,
    const object_factory_parameterst &_object_factory_parameters,
    message_handlert &_message_handler)
    : symbol_table(_symbol_table),
      assume_non_null(_assume_non_null),
      object_factory_parameters(_object_factory_parameters),
      message_handler(_message_handler)
  {
  }

  void create_method_stub_at(
    const typet &expected_type,
    const exprt &ptr,
    const source_locationt &loc,
    const irep_idt &function_id,
    code_blockt &parent_block,
    unsigned insert_before_index,
    bool is_constructor,
    bool update_in_place);

  void create_method_stub(symbolt &symbol);

  void check_method_stub(const irep_idt &);

protected:
  symbol_table_baset &symbol_table;
  bool assume_non_null;
  const object_factory_parameterst &object_factory_parameters;
  message_handlert &message_handler;
};

/// Nondet-initialize an object, including allocating referees for reference
/// fields and nondet-initialising those recursively. Reference fields are
/// nondeterministically assigned either a fresh object or null; arrays are
/// additionally nondeterministically assigned between 0 and
/// `max_nondet_array_length` members.
/// \param expected_type: the expected actual type of `ptr`. We will cast
///   `ptr` to this type and initialize assuming the actual referee has this
///   type.
/// \param ptr: pointer to the memory to initialize
/// \param loc: source location to set for the opaque method stub
/// \param function_id: name of the function we're generated stub code for; used
///   to ensure any generated temporaries are created in the correct scope.
/// \param [out] parent_block: The parent block in which the new instructions
///   will be added.
/// \param insert_before_index: The position in which the new instructions
///   will be added.
/// \param is_constructor: true if we're initialising the `this` pointer of a
///   constructor. In this case the target's class identifier has been set and
///   should not be overridden.
/// \param update_in_place: Whether to generate the nondet in place or not.
void java_simple_method_stubst::create_method_stub_at(
  const typet &expected_type,
  const exprt &ptr,
  const source_locationt &loc,
  const irep_idt &function_id,
  code_blockt &parent_block,
  const unsigned insert_before_index,
  const bool is_constructor,
  const bool update_in_place)
{
  // At this point we know 'ptr' points to an opaque-typed object.
  // We should nondet-initialize it and insert the instructions *after*
  // the offending call at (*parent_block)[insert_before_index].

  INVARIANT_WITH_IREP(
    expected_type.id() == ID_pointer,
    "Nondet initializer result type: expected a pointer",
    expected_type);

  namespacet ns(symbol_table);

  const auto &expected_base = ns.follow(expected_type.subtype());
  if(expected_base.id() != ID_struct)
    return;

  const exprt cast_ptr =
    make_clean_pointer_cast(ptr, to_pointer_type(expected_type), ns);

  exprt to_init = cast_ptr;
  // If it's a constructor the thing we're constructing has already
  // been allocated by this point.
  if(is_constructor)
    to_init = dereference_exprt(to_init, expected_base);

  object_factory_parameterst parameters = object_factory_parameters;
  if(assume_non_null)
    parameters.min_null_tree_depth = 1;

  // Generate new instructions.
  code_blockt new_instructions;
  parameters.function_id = function_id;
  gen_nondet_init(
    to_init,
    new_instructions,
    symbol_table,
    loc,
    is_constructor,
    allocation_typet::DYNAMIC,
    parameters,
    update_in_place ? update_in_placet::MUST_UPDATE_IN_PLACE
                    : update_in_placet::NO_UPDATE_IN_PLACE);

  // Insert new_instructions into parent block.
  if(!new_instructions.statements().empty())
  {
    auto insert_position = parent_block.statements().begin();
    std::advance(insert_position, insert_before_index);
    parent_block.statements().insert(
      insert_position,
      new_instructions.statements().begin(),
      new_instructions.statements().end());
  }
}

/// Replaces sym's value with an opaque method stub. If sym is a
///   constructor function this nondet-initializes `*this` using the function
///   above; otherwise it generates a return value using a similar method.
/// \param symbol: Function symbol to stub
void java_simple_method_stubst::create_method_stub(symbolt &symbol)
{
  code_blockt new_instructions;
  const java_method_typet &required_type = to_java_method_type(symbol.type);

  // synthetic source location that contains the opaque function name only
  source_locationt synthesized_source_location;
  synthesized_source_location.set_function(symbol.name);

  // Initialize the return value or `this` parameter under construction.
  // Note symbol.type is required_type, but with write access
  // Probably required_type should not be const
  const bool is_constructor = required_type.get_is_constructor();
  if(is_constructor)
  {
    const auto &this_argument = required_type.parameters()[0];
    const typet &this_type = this_argument.type();
    symbolt &init_symbol = get_fresh_aux_symbol(
      this_type,
      id2string(symbol.name),
      "to_construct",
      synthesized_source_location,
      ID_java,
      symbol_table);
    const symbol_exprt &init_symbol_expression = init_symbol.symbol_expr();
    code_assignt get_argument(
      init_symbol_expression, symbol_exprt(this_argument.get_identifier()));
    get_argument.add_source_location() = synthesized_source_location;
    new_instructions.add(get_argument);
    create_method_stub_at(
      this_type,
      init_symbol_expression,
      synthesized_source_location,
      symbol.name,
      new_instructions,
      1,
      true,
      false);
  }
  else
  {
    const typet &required_return_type = required_type.return_type();
    if(required_return_type != empty_typet())
    {
      symbolt &to_return_symbol = get_fresh_aux_symbol(
        required_return_type,
        id2string(symbol.name),
        "to_return",
        synthesized_source_location,
        ID_java,
        symbol_table);
      const exprt &to_return = to_return_symbol.symbol_expr();
      if(to_return_symbol.type.id() != ID_pointer)
      {
        object_factory_parameterst parameters = object_factory_parameters;
        if(assume_non_null)
          parameters.min_null_tree_depth = 1;

        gen_nondet_init(
          to_return,
          new_instructions,
          symbol_table,
          source_locationt(),
          false,
          allocation_typet::LOCAL, // Irrelevant as type is primitive
          parameters,
          update_in_placet::NO_UPDATE_IN_PLACE);
      }
      else
        create_method_stub_at(
          required_return_type,
          to_return,
          synthesized_source_location,
          symbol.name,
          new_instructions,
          0,
          false,
          false);
      new_instructions.add(code_returnt(to_return));
    }
  }

  symbol.value = new_instructions;
}

/// Replaces `sym` with a function stub per the function above if it is
///   of suitable type.
/// \param symname: Symbol name to consider stubbing
void java_simple_method_stubst::check_method_stub(const irep_idt &symname)
{
  const symbolt &sym = *symbol_table.lookup(symname);
  if(!sym.is_type && sym.value.id() == ID_nil &&
    sym.type.id() == ID_code &&
    // do not stub internal locking calls as 'create_method_stub' does not
    // automatically create the appropriate symbols for the formal parameters.
    // This means that symex will (rightfully) crash  when it encounters the
    // function call as it will not be able to find symbols for the fromal
    // parameters.
    sym.name !=
      "java::java.lang.Object.monitorenter:(Ljava/lang/Object;)V" &&
    sym.name !=
      "java::java.lang.Object.monitorexit:(Ljava/lang/Object;)V")
  {
    create_method_stub(*symbol_table.get_writeable(symname));
  }
}

void java_generate_simple_method_stub(
  const irep_idt &function_name,
  symbol_table_baset &symbol_table,
  bool assume_non_null,
  const object_factory_parameterst &object_factory_parameters,
  message_handlert &message_handler)
{
  java_simple_method_stubst stub_generator(
    symbol_table, assume_non_null, object_factory_parameters, message_handler);

  stub_generator.check_method_stub(function_name);
}

/// Generates function stubs for most undefined functions in the symbol
///   table, except as forbidden in
///   `java_simple_method_stubst::check_method_stub`.
/// \param symbol_table: Global symbol table
/// \param assume_non_null: If true, generated function stubs will never
///   initialize reference members with null.
/// \param object_factory_parameters: specifies exactly how nondet composite
///   objects should be created-- for example, object graph depth.
/// \param message_handler: Logging
void java_generate_simple_method_stubs(
  symbol_table_baset &symbol_table,
  bool assume_non_null,
  const object_factory_parameterst &object_factory_parameters,
  message_handlert &message_handler)
{
  // The intent here is to apply stub_generator.check_method_stub() to
  // all the identifiers in the symbol table. However this method may alter the
  // symbol table and iterating over a container which is being modified has
  // undefined behaviour. Therefore in order for this to work reliably, we must
  // take a copy of the identifiers in the symbol table and iterate over that,
  // instead of iterating over the symbol table itself.
  std::vector<irep_idt> identifiers;
  identifiers.reserve(symbol_table.symbols.size());
  for(const auto &symbol : symbol_table)
    identifiers.push_back(symbol.first);

  java_simple_method_stubst stub_generator(
    symbol_table, assume_non_null, object_factory_parameters, message_handler);

  for(const auto &identifier : identifiers)
  {
    stub_generator.check_method_stub(identifier);
  }
}
