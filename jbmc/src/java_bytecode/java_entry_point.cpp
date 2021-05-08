/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_entry_point.h"

#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/journalling_symbol_table.h>
#include <util/suffix.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/class_identifier.h>
#include <goto-programs/goto_functions.h>

#include <linking/static_lifetime_init.h>

#include "java_bytecode_instrument.h"
#include "java_bytecode_language.h"
#include "java_object_factory.h"
#include "java_string_literals.h"
#include "java_types.h"
#include "java_utils.h"
#include "nondet.h"

#include <cstring>

#define JAVA_MAIN_METHOD "main:([Ljava/lang/String;)V"

static optionalt<codet> record_return_value(
  const symbolt &function,
  const symbol_table_baset &symbol_table);

static code_blockt record_pointer_parameters(
  const symbolt &function,
  const std::vector<exprt> &arguments,
  const symbol_table_baset &symbol_table);

static codet record_exception(
  const symbolt &function,
  const symbol_table_baset &symbol_table);

void create_java_initialize(symbol_table_baset &symbol_table)
{
  // If __CPROVER_initialize already exists, replace it. It may already exist
  // if a GOTO binary provided it. This behaviour mirrors the ANSI-C frontend.
  symbol_table.remove(INITIALIZE_FUNCTION);

  symbolt initialize;
  initialize.name=INITIALIZE_FUNCTION;
  initialize.base_name=INITIALIZE_FUNCTION;
  initialize.mode=ID_java;

  initialize.type = java_method_typet({}, java_void_type());
  symbol_table.add(initialize);
}

static bool should_init_symbol(const symbolt &sym)
{
  if(sym.type.id()!=ID_code &&
     sym.is_lvalue &&
     sym.is_state_var &&
     sym.is_static_lifetime &&
     sym.mode==ID_java)
  {
    // Consider some sort of annotation indicating a global variable that
    // doesn't require initialisation?
    return !sym.type.get_bool(ID_C_no_initialization_required);
  }

  return is_java_string_literal_id(sym.name);
}

irep_idt get_java_class_literal_initializer_signature()
{
  static irep_idt signature =
    "java::java.lang.Class.cproverInitializeClassLiteral:"
    "(Ljava/lang/String;ZZZZZZZ)V";
  return signature;
}

/// If symbol is a class literal, and an appropriate initializer method exists,
/// return a pointer to its symbol. If not, return null.
/// \param symbol: possible class literal symbol
/// \param symbol_table: table to search
/// \return pointer to the initializer method symbol or null
static const symbolt *get_class_literal_initializer(
  const symbolt &symbol,
  const symbol_table_baset &symbol_table)
{
  if(symbol.value.is_not_nil())
    return nullptr;
  if(symbol.type != struct_tag_typet("java::java.lang.Class"))
    return nullptr;
  if(!has_suffix(id2string(symbol.name), JAVA_CLASS_MODEL_SUFFIX))
    return nullptr;
  return symbol_table.lookup(get_java_class_literal_initializer_signature());
}

static constant_exprt constant_bool(bool val)
{
  return from_integer(val ? 1 : 0, java_boolean_type());
}

static std::unordered_set<irep_idt> init_symbol(
  const symbolt &sym,
  code_blockt &code_block,
  symbol_table_baset &symbol_table,
  const source_locationt &source_location,
  bool assume_init_pointers_not_null,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  bool string_refinement_enabled,
  message_handlert &message_handler)
{
  std::unordered_set<irep_idt> additional_symbols;

  if(
    const symbolt *class_literal_init_method =
      get_class_literal_initializer(sym, symbol_table))
  {
    const std::string &name_str = id2string(sym.name);
    irep_idt class_name =
      name_str.substr(0, name_str.size() - strlen(JAVA_CLASS_MODEL_SUFFIX));
    const symbolt &class_symbol = symbol_table.lookup_ref(class_name);

    bool class_is_array = is_java_array_tag(sym.name);

    journalling_symbol_tablet journalling_table =
      journalling_symbol_tablet::wrap(symbol_table);

    symbol_exprt class_name_literal = get_or_create_string_literal_symbol(
      to_class_type(class_symbol.type).get_tag(),
      journalling_table,
      string_refinement_enabled);

    // If that created any new symbols make sure we initialise those too:
    additional_symbols = journalling_table.get_inserted();

    // Call the literal initializer method instead of a nondet initializer:

    // For arguments we can't parse yet:
    side_effect_expr_nondett nondet_bool(java_boolean_type(), sym.location);

    const auto &java_class_type = to_java_class_type(class_symbol.type);

    // Argument order is: name, isAnnotation, isArray, isInterface,
    // isSynthetic, isLocalClass, isMemberClass, isEnum

    code_function_callt initializer_call(
      class_literal_init_method->symbol_expr(),
      {// this:
       address_of_exprt(sym.symbol_expr()),
       // name:
       address_of_exprt(class_name_literal),
       // isAnnotation:
       constant_bool(java_class_type.get_is_annotation()),
       // isArray:
       constant_bool(class_is_array),
       // isInterface:
       constant_bool(java_class_type.get_interface()),
       // isSynthetic:
       constant_bool(java_class_type.get_synthetic()),
       // isLocalClass:
       nondet_bool,
       // isMemberClass:
       nondet_bool,
       // isEnum:
       constant_bool(java_class_type.get_is_enumeration())});

    // First initialize the object as prior to a constructor:
    namespacet ns(symbol_table);

    auto zero_object = zero_initializer(sym.type, source_locationt(), ns);
    if(!zero_object.has_value())
    {
      messaget message(message_handler);
      message.error() << "failed to zero-initialize " << sym.name
                      << messaget::eom;
      throw 0;
    }
    set_class_identifier(
      to_struct_expr(*zero_object), ns, to_struct_tag_type(sym.type));

    code_block.add(
      std::move(code_frontend_assignt(sym.symbol_expr(), *zero_object)));

    // Then call the init function:
    code_block.add(std::move(initializer_call));
  }
  else if(sym.value.is_nil() && sym.type != java_void_type())
  {
    const bool is_class_model = has_suffix(id2string(sym.name), "@class_model");
    const bool not_allow_null = is_java_string_literal_id(sym.name) ||
                                is_non_null_library_global(sym.name) ||
                                assume_init_pointers_not_null;

    java_object_factory_parameterst parameters = object_factory_parameters;
    if(not_allow_null && !is_class_model)
      parameters.min_null_tree_depth = 1;

    gen_nondet_init(
      sym.symbol_expr(),
      code_block,
      symbol_table,
      source_location,
      false,
      lifetimet::STATIC_GLOBAL,
      parameters,
      pointer_type_selector,
      update_in_placet::NO_UPDATE_IN_PLACE,
      message_handler);
  }
  else if(sym.value.is_not_nil())
  {
    code_frontend_assignt assignment(sym.symbol_expr(), sym.value);
    assignment.add_source_location() = source_location;
    code_block.add(assignment);
  }

  return additional_symbols;
}

void java_static_lifetime_init(
  symbol_table_baset &symbol_table,
  const source_locationt &source_location,
  bool assume_init_pointers_not_null,
  java_object_factory_parameterst object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  bool string_refinement_enabled,
  message_handlert &message_handler)
{
  symbolt &initialize_symbol =
    symbol_table.get_writeable_ref(INITIALIZE_FUNCTION);
  PRECONDITION(initialize_symbol.value.is_nil());
  code_blockt code_block;

  const symbol_exprt rounding_mode =
    symbol_table.lookup_ref(rounding_mode_identifier()).symbol_expr();
  code_block.add(code_frontend_assignt{rounding_mode,
                                       from_integer(0, rounding_mode.type())});

  object_factory_parameters.function_id = initialize_symbol.name;

  // If there are strings given using --string-input-value, we need to add
  // them to the symbol table now, so that they appear in __CPROVER_initialize
  // and we can refer to them later when we initialize input values.
  for(const auto &val : object_factory_parameters.string_input_values)
  {
    // We ignore the return value of the following call, we just need to
    // make sure the string is in the symbol table.
    get_or_create_string_literal_symbol(
      val, symbol_table, string_refinement_enabled);
  }

  // We need to zero out all static variables, or nondet-initialize if they're
  // external. Iterate over a copy of the symtab, as its iterators are
  // invalidated by object_factory:

  std::list<irep_idt> symbol_names;
  for(const auto &entry : symbol_table.symbols)
    symbol_names.push_back(entry.first);

  // Don't use a for-each loop here because the loop extends the list, and the
  // for-each loop may only read `.end()` once.
  for(
    auto symbol_it = symbol_names.begin();
    symbol_it != symbol_names.end();
    ++symbol_it)
  {
    const symbolt &sym = symbol_table.lookup_ref(*symbol_it);
    if(should_init_symbol(sym))
    {
      auto new_symbols = init_symbol(
        sym,
        code_block,
        symbol_table,
        source_location,
        assume_init_pointers_not_null,
        object_factory_parameters,
        pointer_type_selector,
        string_refinement_enabled,
        message_handler);
      symbol_names.insert(
        symbol_names.end(), new_symbols.begin(), new_symbols.end());
    }
  }
  initialize_symbol.value = std::move(code_block);
}

/// Checks whether the given symbol is a valid java main method
/// i.e. it must be public, static, called 'main' and
/// have signature void(String[])
/// \param function: the function symbol
/// \return true if it is a valid main method
bool is_java_main(const symbolt &function)
{
  bool named_main = has_suffix(id2string(function.name), JAVA_MAIN_METHOD);
  const java_method_typet &function_type = to_java_method_type(function.type);
  const auto string_array_type = java_type_from_string("[Ljava/lang/String;");
  // checks whether the function is static and has a single String[] parameter
  bool is_static = !function_type.has_this();
  // this should be implied by the signature
  const java_method_typet::parameterst &parameters = function_type.parameters();
  bool has_correct_type = function_type.return_type().id() == ID_empty &&
                          parameters.size() == 1 &&
                          parameters[0].type().full_eq(*string_array_type);
  bool public_access = function_type.get(ID_access) == ID_public;
  return named_main && is_static && has_correct_type && public_access;
}

std::pair<code_blockt, std::vector<exprt>> java_build_arguments(
  const symbolt &function,
  symbol_table_baset &symbol_table,
  bool assume_init_pointers_not_null,
  java_object_factory_parameterst object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler)
{
  const java_method_typet &function_type = to_java_method_type(function.type);
  const java_method_typet::parameterst &parameters = function_type.parameters();

  code_blockt init_code;
  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());

  // certain method arguments cannot be allowed to be null, we set the following
  // variable to true iff the method under test is the "main" method, which will
  // be called (by the jvm) with arguments that are never null
  bool is_main = is_java_main(function);

  // we iterate through all the parameters of the function under test, allocate
  // an object for that parameter (recursively allocating other objects
  // necessary to initialize it), and mark such object using `code_inputt`.
  for(std::size_t param_number=0;
      param_number<parameters.size();
      param_number++)
  {
    const java_method_typet::parametert &p = parameters[param_number];
    const irep_idt base_name=p.get_base_name().empty()?
      ("argument#"+std::to_string(param_number)):p.get_base_name();

    // true iff this parameter is the `this` pointer of the method, which cannot
    // be null
    bool is_this=(param_number==0) && parameters[param_number].get_this();

    if(is_this && function_type.get_is_constructor())
    {
      const symbol_exprt result = fresh_java_symbol(
                                    p.type(),
                                    "this_parameter",
                                    function.location,
                                    function.name,
                                    symbol_table)
                                    .symbol_expr();
      main_arguments[param_number] = result;
      init_code.add(code_declt{result});
      init_code.add(code_frontend_assignt{
        result,
        side_effect_exprt{ID_java_new, {}, p.type(), function.location}});
      continue;
    }

    java_object_factory_parameterst factory_parameters =
      object_factory_parameters;
    // only pointer must be non-null
    if(assume_init_pointers_not_null || is_this)
      factory_parameters.min_null_tree_depth = 1;
    // in main() also the array elements of the argument must be non-null
    if(is_main)
      factory_parameters.min_null_tree_depth = 2;

    factory_parameters.function_id = goto_functionst::entry_point();

    namespacet ns(symbol_table);

    // Generate code to allocate and non-deterministicaly initialize the
    // argument, if the argument has different possible object types (e.g., from
    // casts in the function body), then choose one in a non-deterministic way.
    const auto alternatives =
      pointer_type_selector.get_parameter_alternative_types(
        function.name, p.get_identifier(), ns);
    if(alternatives.empty())
    {
      main_arguments[param_number] = object_factory(
        p.type(),
        base_name,
        init_code,
        symbol_table,
        factory_parameters,
        lifetimet::DYNAMIC,
        function.location,
        pointer_type_selector,
        message_handler);
    }
    else
    {
      INVARIANT(!is_this, "We cannot have different types for `this` here");
      // create a non-deterministic switch between all possible values for the
      // type of the parameter.

      // the idea is to get a new symbol for the parameter value `tmp`

      // then add a non-deterministic switch over all possible input types,
      // construct the object type at hand and assign to `tmp`

      // switch(...)
      // {
      //   case obj1:
      //     tmp_expr = object_factory(...)
      //     param = tmp_expr
      //     break
      //   ...
      // }
      // method(..., param, ...)
      //

      const symbolt result_symbol = fresh_java_symbol(
        p.type(),
        "nondet_parameter_" + std::to_string(param_number),
        function.location,
        function.name,
        symbol_table);
      main_arguments[param_number] = result_symbol.symbol_expr();

      std::vector<codet> cases;
      cases.reserve(alternatives.size());
      for(const auto &type : alternatives)
      {
        code_blockt init_code_for_type;
        exprt init_expr_for_parameter = object_factory(
          java_reference_type(type),
          id2string(base_name) + "_alternative_" +
            id2string(type.get_identifier()),
          init_code_for_type,
          symbol_table,
          factory_parameters,
          lifetimet::DYNAMIC,
          function.location,
          pointer_type_selector,
          message_handler);
        init_code_for_type.add(code_frontend_assignt(
          result_symbol.symbol_expr(),
          typecast_exprt(init_expr_for_parameter, p.type())));
        cases.push_back(init_code_for_type);
      }

      init_code.add(
        generate_nondet_switch(
          id2string(function.name) + "_" + std::to_string(param_number),
          cases,
          java_int_type(),
          ID_java,
          function.location,
          symbol_table));
    }

    // record as an input
    init_code.add(
      code_inputt{base_name, main_arguments[param_number], function.location});
  }

  return make_pair(init_code, main_arguments);
}

/// Mark return value, pointer type parameters and the exception as outputs.
static code_blockt java_record_outputs(
  const symbolt &function,
  const exprt::operandst &main_arguments,
  symbol_table_baset &symbol_table)
{
  code_blockt init_code;

  if(auto return_value = record_return_value(function, symbol_table))
  {
    init_code.add(std::move(*return_value));
  }

  init_code.append(
    record_pointer_parameters(function, main_arguments, symbol_table));

  init_code.add(record_exception(function, symbol_table));

  return init_code;
}

static optionalt<codet> record_return_value(
  const symbolt &function,
  const symbol_table_baset &symbol_table)
{
  if(to_java_method_type(function.type).return_type() == java_void_type())
    return {};

  const symbolt &return_symbol =
    symbol_table.lookup_ref(JAVA_ENTRY_POINT_RETURN_SYMBOL);

  return code_outputt{
    return_symbol.base_name, return_symbol.symbol_expr(), function.location};
}

static code_blockt record_pointer_parameters(
  const symbolt &function,
  const std::vector<exprt> &arguments,
  const symbol_table_baset &symbol_table)
{
  const java_method_typet::parameterst &parameters =
    to_java_method_type(function.type).parameters();

  code_blockt init_code;

  for(std::size_t param_number = 0; param_number < parameters.size();
      param_number++)
  {
    const symbolt &p_symbol =
      symbol_table.lookup_ref(parameters[param_number].get_identifier());

    if(!can_cast_type<pointer_typet>(p_symbol.type))
      continue;

    init_code.add(code_outputt{
      p_symbol.base_name, arguments[param_number], function.location});
  }
  return init_code;
}

static codet record_exception(
  const symbolt &function,
  const symbol_table_baset &symbol_table)
{
  // retrieve the exception variable
  const symbolt &exc_symbol =
    symbol_table.lookup_ref(JAVA_ENTRY_POINT_EXCEPTION_SYMBOL);

  // record exceptional return variable as output
  return code_outputt{
    exc_symbol.base_name, exc_symbol.symbol_expr(), function.location};
}

main_function_resultt get_main_symbol(
  const symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  // find main symbol
  if(config.main.has_value())
  {
    std::string error_message;
    irep_idt main_symbol_id = resolve_friendly_method_name(
      config.main.value(), symbol_table, error_message);

    if(main_symbol_id.empty())
    {
      message.error()
        << "main symbol resolution failed: " << error_message << messaget::eom;
      return main_function_resultt::Error;
    }

    const symbolt *symbol = symbol_table.lookup(main_symbol_id);
    INVARIANT(
      symbol != nullptr,
      "resolve_friendly_method_name should return a symbol-table identifier");

    return *symbol; // Return found function
  }
  else
  {
    // are we given a main class?
    if(main_class.empty())
    {
      // no, but we allow this situation to output symbol table,
      // goto functions, etc
      return main_function_resultt::NotFound;
    }

    std::string entry_method =
      "java::" + id2string(main_class) + "." + JAVA_MAIN_METHOD;
    const symbolt *symbol = symbol_table.lookup(entry_method);

    // has the class a correct main method?
    if(!symbol || !is_java_main(*symbol))
    {
      // no, but we allow this situation to output symbol table,
      // goto functions, etc
      return main_function_resultt::NotFound;
    }

    return *symbol;
  }
}

bool java_entry_point(
  symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  bool string_refinement_enabled,
  const build_argumentst &build_arguments)
{
  // check if the entry point is already there
  if(symbol_table.symbols.find(goto_functionst::entry_point())!=
     symbol_table.symbols.end())
    return false; // silently ignore

  messaget message(message_handler);
  main_function_resultt res=
    get_main_symbol(symbol_table, main_class, message_handler);
  if(!res.is_success())
    return true;
  symbolt symbol=res.main_function;

  assert(symbol.type.id()==ID_code);

  return generate_java_start_function(
    symbol,
    symbol_table,
    message_handler,
    assert_uncaught_exceptions,
    object_factory_parameters,
    pointer_type_selector,
    build_arguments);
}

bool generate_java_start_function(
  const symbolt &symbol,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  const build_argumentst &build_arguments)
{
  messaget message(message_handler);
  code_blockt init_code;

  // build call to initialization function
  {
    symbol_tablet::symbolst::const_iterator init_it=
      symbol_table.symbols.find(INITIALIZE_FUNCTION);

    if(init_it==symbol_table.symbols.end())
    {
      message.error() << "failed to find " INITIALIZE_FUNCTION " symbol"
                      << messaget::eom;
      return true; // give up with error
    }

    code_function_callt call_init(init_it->second.symbol_expr());
    call_init.add_source_location()=symbol.location;

    init_code.add(std::move(call_init));
  }

  // build call to the main method, of the form
  // return = main_method(arg1, arg2, ..., argn)
  // where return is a new variable
  // and arg1 ... argn are constructed below as well

  source_locationt loc=symbol.location;
  loc.set_function(symbol.name);
  source_locationt &dloc=loc;

  // function to call
  code_function_callt call_main(symbol.symbol_expr());
  call_main.add_source_location()=dloc;
  call_main.function().add_source_location()=dloc;

  // if the method return type is not void, store return value in a new variable
  // named 'return'
  if(to_java_method_type(symbol.type).return_type() != java_void_type())
  {
    auxiliary_symbolt return_symbol;
    return_symbol.mode=ID_java;
    return_symbol.is_static_lifetime=false;
    return_symbol.name=JAVA_ENTRY_POINT_RETURN_SYMBOL;
    return_symbol.base_name = "return'";
    return_symbol.type = to_java_method_type(symbol.type).return_type();

    symbol_table.add(return_symbol);
    call_main.lhs()=return_symbol.symbol_expr();
  }

  // add the exceptional return value
  auxiliary_symbolt exc_symbol;
  exc_symbol.mode=ID_java;
  exc_symbol.name=JAVA_ENTRY_POINT_EXCEPTION_SYMBOL;
  exc_symbol.base_name=exc_symbol.name;
  exc_symbol.type = java_reference_type(java_void_type());
  symbol_table.add(exc_symbol);

  // Zero-initialise the top-level exception catch variable:
  init_code.add(code_frontend_assignt(
    exc_symbol.symbol_expr(),
    null_pointer_exprt(to_pointer_type(exc_symbol.type))));

  // create code that allocates the objects used as test arguments and
  // non-deterministically initializes them
  const std::pair<code_blockt, std::vector<exprt>> main_arguments =
    build_arguments(symbol, symbol_table);
  init_code.append(main_arguments.first);
  call_main.arguments() = main_arguments.second;

  // Create target labels for the toplevel exception handler:
  code_labelt toplevel_catch("toplevel_catch", code_skipt());
  code_labelt after_catch("after_catch", code_skipt());

  code_blockt call_block;

  // Push a universal exception handler:
  // Catch all exceptions:
  // This is equivalent to catching Throwable, but also works if some of
  // the class hierarchy is missing so that we can't determine that
  // the thrown instance is an indirect child of Throwable
  code_push_catcht push_universal_handler(
    irep_idt(), toplevel_catch.get_label());
  irept catch_type_list(ID_exception_list);
  irept catch_target_list(ID_label);

  call_block.add(std::move(push_universal_handler));

  // we insert the call to the method AFTER the argument initialization code
  call_block.add(std::move(call_main));

  // Pop the handler:
  code_pop_catcht pop_handler;
  call_block.add(std::move(pop_handler));
  init_code.add(std::move(call_block));

  // Normal return: skip the exception handler:
  init_code.add(code_gotot(after_catch.get_label()));

  // Exceptional return: catch and assign to exc_symbol.
  code_landingpadt landingpad(exc_symbol.symbol_expr());
  init_code.add(std::move(toplevel_catch));
  init_code.add(std::move(landingpad));

  // Converge normal and exceptional return:
  init_code.add(std::move(after_catch));

  // Mark return value, pointer type parameters and the exception as outputs.
  init_code.append(
    java_record_outputs(symbol, main_arguments.second, symbol_table));

  // add uncaught-exception check if requested
  if(assert_uncaught_exceptions)
  {
    java_bytecode_instrument_uncaught_exceptions(
      init_code, exc_symbol, symbol.location);
  }

  // create a symbol for the __CPROVER__start function, associate the code that
  // we just built and register it in the symbol table
  symbolt new_symbol;

  new_symbol.name=goto_functionst::entry_point();
  new_symbol.type = java_method_typet({}, java_void_type());
  new_symbol.value.swap(init_code);
  new_symbol.mode=ID_java;

  if(!symbol_table.insert(std::move(new_symbol)).second)
  {
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }

  return false;
}
