/*******************************************************************\

Module: Replace bodies of goto functions

Author: Diffblue Ltd.

\*******************************************************************/

#include "generate_function_bodies.h"

#include <ansi-c/c_nondet_symbol_factory.h>

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/make_unique.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/string2int.h>
#include <util/string_utils.h>

void generate_function_bodiest::generate_function_body(
  goto_functiont &function,
  symbol_tablet &symbol_table,
  const irep_idt &function_name) const
{
  PRECONDITION(!function.body_available());
  generate_parameter_names(function, symbol_table, function_name);
  generate_function_body_impl(function, symbol_table, function_name);
}

void generate_function_bodiest::generate_parameter_names(
  goto_functiont &function,
  symbol_tablet &symbol_table,
  const irep_idt &function_name) const
{
  auto &function_symbol = symbol_table.get_writeable_ref(function_name);
  auto &parameters = to_code_type(function_symbol.type).parameters();

  int param_counter = 0;
  for(auto &parameter : parameters)
  {
    if(parameter.get_identifier().empty())
    {
      const std::string param_base_name =
        parameter.get_base_name().empty()
          ? "__param$" + std::to_string(param_counter++)
          : id2string(parameter.get_base_name());
      irep_idt new_param_identifier =
        id2string(function_name) + "::" + param_base_name;
      parameter.set_base_name(param_base_name);
      parameter.set_identifier(new_param_identifier);
      parameter_symbolt new_param_sym;
      new_param_sym.name = new_param_identifier;
      new_param_sym.type = parameter.type();
      new_param_sym.base_name = param_base_name;
      new_param_sym.mode = function_symbol.mode;
      new_param_sym.module = function_symbol.module;
      new_param_sym.location = function_symbol.location;
      symbol_table.add(new_param_sym);
    }
  }
  function.set_parameter_identifiers(to_code_type(function_symbol.type));
}

class assume_false_generate_function_bodiest : public generate_function_bodiest
{
protected:
  void generate_function_body_impl(
    goto_functiont &function,
    symbol_tablet &symbol_table,
    const irep_idt &function_name) const override
  {
    auto const &function_symbol = symbol_table.lookup_ref(function_name);
    // NOLINTNEXTLINE
    auto add_instruction = [&](goto_programt::instructiont &&i) {
      auto instruction = function.body.add(std::move(i));
      instruction->source_location_nonconst() = function_symbol.location;
      return instruction;
    };
    add_instruction(goto_programt::make_assumption(false_exprt()));
    add_instruction(goto_programt::make_end_function());
  }
};

class assert_false_generate_function_bodiest : public generate_function_bodiest
{
protected:
  void generate_function_body_impl(
    goto_functiont &function,
    symbol_tablet &symbol_table,
    const irep_idt &function_name) const override
  {
    auto const &function_symbol = symbol_table.lookup_ref(function_name);
    // NOLINTNEXTLINE
    auto add_instruction = [&](goto_programt::instructiont &&i) {
      auto instruction = function.body.add(std::move(i));
      instruction->source_location_nonconst() = function_symbol.location;
      instruction->source_location_nonconst().set_function(function_name);
      return instruction;
    };
    auto assert_instruction =
      add_instruction(goto_programt::make_assertion(false_exprt()));
    const namespacet ns(symbol_table);
    std::ostringstream comment_stream;
    comment_stream << id2string(ID_assertion) << " "
                   << format(assert_instruction->condition());
    assert_instruction->source_location_nonconst().set_comment(
      comment_stream.str());
    assert_instruction->source_location_nonconst().set_property_class(
      ID_assertion);
    add_instruction(goto_programt::make_end_function());
  }
};

class assert_false_then_assume_false_generate_function_bodiest
  : public generate_function_bodiest
{
protected:
  void generate_function_body_impl(
    goto_functiont &function,
    symbol_tablet &symbol_table,
    const irep_idt &function_name) const override
  {
    auto const &function_symbol = symbol_table.lookup_ref(function_name);
    // NOLINTNEXTLINE
    auto add_instruction = [&](goto_programt::instructiont &&i) {
      auto instruction = function.body.add(std::move(i));
      instruction->source_location_nonconst() = function_symbol.location;
      instruction->source_location_nonconst().set_function(function_name);
      return instruction;
    };
    auto assert_instruction =
      add_instruction(goto_programt::make_assertion(false_exprt()));
    const namespacet ns(symbol_table);
    std::ostringstream comment_stream;
    comment_stream << id2string(ID_assertion) << " "
                   << format(assert_instruction->condition());
    assert_instruction->source_location_nonconst().set_comment(
      comment_stream.str());
    assert_instruction->source_location_nonconst().set_property_class(
      ID_assertion);
    add_instruction(goto_programt::make_assumption(false_exprt()));
    add_instruction(goto_programt::make_end_function());
  }
};

class havoc_generate_function_bodiest : public generate_function_bodiest
{
public:
  havoc_generate_function_bodiest(
    std::vector<irep_idt> globals_to_havoc,
    std::regex parameters_to_havoc,
    const c_object_factory_parameterst &object_factory_parameters,
    message_handlert &message_handler)
    : generate_function_bodiest(),
      globals_to_havoc(std::move(globals_to_havoc)),
      parameters_to_havoc(std::move(parameters_to_havoc)),
      object_factory_parameters(object_factory_parameters),
      message(message_handler)
  {
  }

  havoc_generate_function_bodiest(
    std::vector<irep_idt> globals_to_havoc,
    std::vector<std::size_t> param_numbers_to_havoc,
    const c_object_factory_parameterst &object_factory_parameters,
    message_handlert &message_handler)
    : generate_function_bodiest(),
      globals_to_havoc(std::move(globals_to_havoc)),
      param_numbers_to_havoc(std::move(param_numbers_to_havoc)),
      object_factory_parameters(object_factory_parameters),
      message(message_handler)
  {
  }

private:
  void havoc_expr_rec(
    const exprt &lhs,
    const std::size_t initial_depth,
    const source_locationt &source_location,
    const irep_idt &function_id,
    symbol_tablet &symbol_table,
    goto_programt &dest) const
  {
    symbol_factoryt symbol_factory(
      symbol_table,
      source_location,
      function_id,
      object_factory_parameters,
      lifetimet::DYNAMIC);

    code_blockt assignments;

    symbol_factory.gen_nondet_init(
      assignments,
      lhs,
      initial_depth,
      symbol_factoryt::recursion_sett(),
      false); // do not initialize const objects at the top level

    code_blockt init_code;

    symbol_factory.declare_created_symbols(init_code);
    init_code.append(assignments);

    goto_programt tmp_dest;
    goto_convert(
      init_code, symbol_table, tmp_dest, message.get_message_handler(), ID_C);

    dest.destructive_append(tmp_dest);
  }

  bool should_havoc_param(
    const std::string &param_name,
    std::size_t param_number) const
  {
    if(parameters_to_havoc.has_value())
    {
      return std::regex_match(param_name, *parameters_to_havoc);
    }
    else
    {
      CHECK_RETURN(param_numbers_to_havoc.has_value());
      return std::binary_search(
        param_numbers_to_havoc->begin(),
        param_numbers_to_havoc->end(),
        param_number);
    }
  }

protected:
  void generate_function_body_impl(
    goto_functiont &function,
    symbol_tablet &symbol_table,
    const irep_idt &function_name) const override
  {
    const namespacet ns(symbol_table);
    // some user input checking
    if(param_numbers_to_havoc.has_value() && !param_numbers_to_havoc->empty())
    {
      auto max_param_number = std::max_element(
        param_numbers_to_havoc->begin(), param_numbers_to_havoc->end());
      if(*max_param_number >= function.parameter_identifiers.size())
      {
        throw invalid_command_line_argument_exceptiont{
          "function " + id2string(function_name) + " does not take " +
            std::to_string(*max_param_number + 1) + " arguments",
          "--generate-havocing-body"};
      }
      for(const auto number : *param_numbers_to_havoc)
      {
        const auto &parameter = function.parameter_identifiers[number];
        const symbolt &parameter_symbol = ns.lookup(parameter);
        if(parameter_symbol.type.id() != ID_pointer)
        {
          throw invalid_command_line_argument_exceptiont{
            "argument number " + std::to_string(number) + " of function " +
              id2string(function_name) + " is not a pointer",
            "--generate-havocing-body"};
        }
      }
    }

    auto const &function_symbol = symbol_table.lookup_ref(function_name);
    // NOLINTNEXTLINE
    auto add_instruction = [&](goto_programt::instructiont &&i) {
      auto instruction = function.body.add(std::move(i));
      instruction->source_location_nonconst() = function_symbol.location;
      return instruction;
    };

    for(std::size_t i = 0; i < function.parameter_identifiers.size(); ++i)
    {
      const auto &parameter = function.parameter_identifiers[i];
      const symbolt &parameter_symbol = ns.lookup(parameter);
      if(
        parameter_symbol.type.id() == ID_pointer &&
        !to_pointer_type(parameter_symbol.type)
           .base_type()
           .get_bool(ID_C_constant) &&
        should_havoc_param(id2string(parameter_symbol.base_name), i))
      {
        auto goto_instruction =
          add_instruction(goto_programt::make_incomplete_goto(equal_exprt(
            parameter_symbol.symbol_expr(),
            null_pointer_exprt(to_pointer_type(parameter_symbol.type)))));

        dereference_exprt dereference_expr(
          parameter_symbol.symbol_expr(),
          to_pointer_type(parameter_symbol.type).base_type());

        goto_programt dest;
        havoc_expr_rec(
          dereference_expr,
          1, // depth 1 since we pass the dereferenced pointer
          function_symbol.location,
          function_name,
          symbol_table,
          dest);

        function.body.destructive_append(dest);

        auto label_instruction = add_instruction(goto_programt::make_skip());
        goto_instruction->complete_goto(label_instruction);
      }
    }

    for(auto const &global_id : globals_to_havoc)
    {
      auto const &global_sym = symbol_table.lookup_ref(global_id);

      goto_programt dest;

      havoc_expr_rec(
        symbol_exprt(global_sym.name, global_sym.type),
        0,
        function_symbol.location,
        irep_idt(),
        symbol_table,
        dest);

      function.body.destructive_append(dest);
    }

    const typet &return_type = to_code_type(function_symbol.type).return_type();
    if(return_type != empty_typet())
    {
      typet type(return_type);
      type.remove(ID_C_constant);

      symbolt &aux_symbol = get_fresh_aux_symbol(
        type,
        id2string(function_name),
        "return_value",
        function_symbol.location,
        ID_C,
        symbol_table);

      aux_symbol.is_static_lifetime = false;

      add_instruction(goto_programt::make_decl(aux_symbol.symbol_expr()));

      goto_programt dest;

      havoc_expr_rec(
        aux_symbol.symbol_expr(),
        0,
        function_symbol.location,
        function_name,
        symbol_table,
        dest);

      function.body.destructive_append(dest);

      exprt return_expr =
        typecast_exprt::conditional_cast(aux_symbol.symbol_expr(), return_type);

      add_instruction(
        goto_programt::make_set_return_value(std::move(return_expr)));

      add_instruction(goto_programt::make_dead(aux_symbol.symbol_expr()));
    }

    add_instruction(goto_programt::make_end_function());

    remove_skip(function.body);
  }

private:
  const std::vector<irep_idt> globals_to_havoc;
  optionalt<std::regex> parameters_to_havoc;
  optionalt<std::vector<std::size_t>> param_numbers_to_havoc;
  const c_object_factory_parameterst &object_factory_parameters;
  mutable messaget message;
};

class generate_function_bodies_errort : public std::runtime_error
{
public:
  explicit generate_function_bodies_errort(const std::string &reason)
    : runtime_error(reason)
  {
  }
};

/// Create the type that actually generates the functions.
/// \see generate_function_bodies for the syntax of the options parameter
std::unique_ptr<generate_function_bodiest> generate_function_bodies_factory(
  const std::string &options,
  const c_object_factory_parameterst &object_factory_parameters,
  const symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(options.empty() || options == "nondet-return")
  {
    return util_make_unique<havoc_generate_function_bodiest>(
      std::vector<irep_idt>{},
      std::regex{},
      object_factory_parameters,
      message_handler);
  }

  if(options == "assume-false")
  {
    return util_make_unique<assume_false_generate_function_bodiest>();
  }

  if(options == "assert-false")
  {
    return util_make_unique<assert_false_generate_function_bodiest>();
  }

  if(options == "assert-false-assume-false")
  {
    return util_make_unique<
      assert_false_then_assume_false_generate_function_bodiest>();
  }

  const std::vector<std::string> option_components = split_string(options, ',');
  if(!option_components.empty() && option_components[0] == "havoc")
  {
    std::regex globals_regex;
    std::regex params_regex;
    std::vector<std::size_t> param_numbers;
    for(std::size_t i = 1; i < option_components.size(); ++i)
    {
      const std::vector<std::string> key_value_pair =
        split_string(option_components[i], ':');
      if(key_value_pair.size() != 2)
      {
        throw generate_function_bodies_errort(
          "Expected key_value_pair of form argument:value");
      }
      if(key_value_pair[0] == "globals")
      {
        globals_regex = key_value_pair[1];
      }
      else if(key_value_pair[0] == "params")
      {
        auto param_identifiers = split_string(key_value_pair[1], ';');
        if(param_identifiers.size() == 1)
        {
          auto maybe_nondet_param_number =
            string2optional_size_t(param_identifiers.back());
          if(!maybe_nondet_param_number.has_value())
          {
            params_regex = key_value_pair[1];
            continue;
          }
        }
        std::transform(
          param_identifiers.begin(),
          param_identifiers.end(),
          std::back_inserter(param_numbers),
          [](const std::string &param_id) {
            auto maybe_nondet_param_number = string2optional_size_t(param_id);
            INVARIANT(
              maybe_nondet_param_number.has_value(),
              param_id + " not a number");
            return *maybe_nondet_param_number;
          });
        std::sort(param_numbers.begin(), param_numbers.end());
      }
      else
      {
        throw generate_function_bodies_errort(
          "Unknown option \"" + key_value_pair[0] + "\"");
      }
    }
    std::vector<irep_idt> globals_to_havoc;
    namespacet ns(symbol_table);
    messaget messages(message_handler);
    const std::regex cprover_prefix = std::regex("__CPROVER.*");
    for(auto const &symbol : symbol_table.symbols)
    {
      if(
        symbol.second.is_lvalue && symbol.second.is_static_lifetime &&
        std::regex_match(id2string(symbol.first), globals_regex))
      {
        if(std::regex_match(id2string(symbol.first), cprover_prefix))
        {
          messages.warning() << "generate function bodies: "
                             << "matched global '" << id2string(symbol.first)
                             << "' begins with __CPROVER, "
                             << "havoc-ing this global may interfere"
                             << " with analysis" << messaget::eom;
        }
        globals_to_havoc.push_back(symbol.first);
      }
    }
    if(param_numbers.empty())
      return util_make_unique<havoc_generate_function_bodiest>(
        std::move(globals_to_havoc),
        std::move(params_regex),
        object_factory_parameters,
        message_handler);
    else
      return util_make_unique<havoc_generate_function_bodiest>(
        std::move(globals_to_havoc),
        std::move(param_numbers),
        object_factory_parameters,
        message_handler);
  }
  throw generate_function_bodies_errort("Can't parse \"" + options + "\"");
}

/// Generate function bodies with some default behavior: assert-false,
///   assume-false, assert-false-assume-false, havoc, nondet-return.
/// \param functions_regex: Specifies the functions whose body should be
///   generated
/// \param generate_function_body: Specifies what kind of body to generate
/// \param model: The goto-model in which to generate the function bodies
/// \param message_handler: Destination for status/warning messages
void generate_function_bodies(
  const std::regex &functions_regex,
  const generate_function_bodiest &generate_function_body,
  goto_modelt &model,
  message_handlert &message_handler)
{
  messaget messages(message_handler);
  const std::regex cprover_prefix = std::regex("__CPROVER.*");
  bool did_generate_body = false;
  for(auto &function : model.goto_functions.function_map)
  {
    if(
      !function.second.body_available() &&
      std::regex_match(id2string(function.first), functions_regex))
    {
      if(std::regex_match(id2string(function.first), cprover_prefix))
      {
        messages.warning() << "generate function bodies: matched function '"
                           << id2string(function.first)
                           << "' begins with __CPROVER "
                           << "the generated body for this function "
                           << "may interfere with analysis" << messaget::eom;
      }
      did_generate_body = true;
      generate_function_body.generate_function_body(
        function.second, model.symbol_table, function.first);
    }
  }
  if(!did_generate_body)
  {
    messages.warning()
      << "generate function bodies: No function name matched regex"
      << messaget::eom;
  }
}

void generate_function_bodies(
  const std::string &function_name,
  const std::string &call_site_id,
  const generate_function_bodiest &generate_function_body,
  goto_modelt &model,
  message_handlert &message_handler)
{
  PRECONDITION(!has_prefix(function_name, CPROVER_PREFIX));
  auto call_site_number = string2optional_size_t(call_site_id);
  PRECONDITION(call_site_number.has_value());

  messaget messages(message_handler);

  bool found = false;
  irep_idt function_mode;
  typet function_type;

  // get the mode and type from symbol table
  for(auto const &symbol_pair : model.symbol_table)
  {
    auto const symbol = symbol_pair.second;
    if(symbol.type.id() == ID_code && symbol.name == function_name)
    {
      function_mode = symbol.mode;
      function_type = symbol.type;
      found = true;
      break;
    }
  }
  CHECK_RETURN(found);

  // add function of the right name to the symbol table
  symbolt havoc_function_symbol{};
  havoc_function_symbol.name = havoc_function_symbol.base_name =
    havoc_function_symbol.pretty_name = function_name + "." + call_site_id;

  havoc_function_symbol.is_lvalue = true;
  havoc_function_symbol.mode = function_mode;
  havoc_function_symbol.type = function_type;

  model.symbol_table.insert(havoc_function_symbol);

  auto const &generated_havoc =
    model.symbol_table.lookup_ref(havoc_function_symbol.name);

  // convert to get the function stub to goto-model
  goto_convert(model.symbol_table, model.goto_functions, message_handler);

  // now generate body as above
  for(auto &function : model.goto_functions.function_map)
  {
    if(
      !function.second.body_available() &&
      havoc_function_symbol.name == id2string(function.first))
    {
      generate_function_body.generate_function_body(
        function.second, model.symbol_table, function.first);
    }
  }

  auto is_havoc_function_call = [&function_name](const exprt &expr) {
    if(expr.id() != ID_symbol)
      return false;
    std::string called_function_name =
      id2string(to_symbol_expr(expr).get_identifier());
    if(called_function_name == function_name)
      return true;

    return (has_prefix(called_function_name, function_name + "."));
  };

  // finally, rename the (right) call site
  std::size_t counter = 0;
  for(auto &function : model.goto_functions.function_map)
  {
    for(auto &instruction : function.second.body.instructions)
    {
      if(instruction.is_function_call())
      {
        auto &called_function =
          to_code_function_call(instruction.code_nonconst()).function();
        if(is_havoc_function_call(called_function))
        {
          if(++counter == *call_site_number)
          {
            called_function = generated_havoc.symbol_expr();
            return;
          }
        }
      }
    }
  }
}
