/*******************************************************************\

Module: Replace bodies of goto functions

Author: Diffblue Ltd.

\*******************************************************************/

#include "generate_function_bodies.h"

#include <ansi-c/c_nondet_symbol_factory.h>
#include <ansi-c/c_object_factory_parameters.h>

#include <goto-programs/goto_convert.h>
#include <goto-programs/remove_skip.h>

#include <util/arith_tools.h>
#include <util/format_expr.h>
#include <util/make_unique.h>
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
  const namespacet ns(symbol_table);
  int param_counter = 0;
  for(auto &parameter : function.type.parameters())
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
      auto const &function_symbol = symbol_table.lookup_ref(function_name);
      new_param_sym.mode = function_symbol.mode;
      new_param_sym.module = function_symbol.module;
      new_param_sym.location = function_symbol.location;
      symbol_table.add(new_param_sym);
    }
  }
  auto &function_symbol = symbol_table.get_writeable_ref(function_name);
  function_symbol.type = function.type;
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
    auto add_instruction = [&]() {
      auto instruction = function.body.add_instruction();
      instruction->function = function_name;
      instruction->source_location = function_symbol.location;
      return instruction;
    };
    auto assume_instruction = add_instruction();
    assume_instruction->make_assumption(false_exprt());
    auto end_instruction = add_instruction();
    end_instruction->make_end_function();
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
    auto add_instruction = [&]() {
      auto instruction = function.body.add_instruction();
      instruction->function = function_name;
      instruction->source_location = function_symbol.location;
      instruction->source_location.set_function(function_name);
      return instruction;
    };
    auto assert_instruction = add_instruction();
    assert_instruction->make_assertion(false_exprt());
    const namespacet ns(symbol_table);
    std::ostringstream comment_stream;
    comment_stream << id2string(ID_assertion) << " "
                   << format(assert_instruction->guard);
    assert_instruction->source_location.set_comment(comment_stream.str());
    assert_instruction->source_location.set_property_class(ID_assertion);
    auto end_instruction = add_instruction();
    end_instruction->make_end_function();
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
    auto add_instruction = [&]() {
      auto instruction = function.body.add_instruction();
      instruction->function = function_name;
      instruction->source_location = function_symbol.location;
      instruction->source_location.set_function(function_name);
      return instruction;
    };
    auto assert_instruction = add_instruction();
    assert_instruction->make_assertion(false_exprt());
    assert_instruction->source_location.set_function(function_name);
    const namespacet ns(symbol_table);
    std::ostringstream comment_stream;
    comment_stream << id2string(ID_assertion) << " "
                   << format(assert_instruction->guard);
    assert_instruction->source_location.set_comment(comment_stream.str());
    assert_instruction->source_location.set_property_class(ID_assertion);
    auto assume_instruction = add_instruction();
    assume_instruction->make_assumption(false_exprt());
    auto end_instruction = add_instruction();
    end_instruction->make_end_function();
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

private:
  void havoc_expr_rec(
    const exprt &lhs,
    const std::size_t initial_depth,
    const source_locationt &source_location,
    symbol_tablet &symbol_table,
    goto_programt &dest) const
  {
    symbol_factoryt symbol_factory(
      symbol_table,
      source_location,
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

protected:
  void generate_function_body_impl(
    goto_functiont &function,
    symbol_tablet &symbol_table,
    const irep_idt &function_name) const override
  {
    auto const &function_symbol = symbol_table.lookup_ref(function_name);
    // NOLINTNEXTLINE
    auto add_instruction = [&]() {
      auto instruction = function.body.add_instruction();
      instruction->function = function_name;
      instruction->source_location = function_symbol.location;
      return instruction;
    };
    const namespacet ns(symbol_table);
    for(auto const &parameter : function.type.parameters())
    {
      if(
        parameter.type().id() == ID_pointer &&
        !parameter.type().subtype().get_bool(ID_C_constant) &&
        std::regex_match(
          id2string(parameter.get_base_name()), parameters_to_havoc))
      {
        auto goto_instruction = add_instruction();

        const irep_idt base_name = parameter.get_base_name();
        CHECK_RETURN(!base_name.empty());

        dereference_exprt dereference_expr(
          symbol_exprt(parameter.get_identifier(), parameter.type()),
          parameter.type().subtype());

        goto_programt dest;
        havoc_expr_rec(
          dereference_expr,
          1, // depth 1 since we pass the dereferenced pointer
          function_symbol.location,
          symbol_table,
          dest);

        function.body.destructive_append(dest);

        auto label_instruction = add_instruction();
        goto_instruction->make_goto(
          label_instruction,
          equal_exprt(
            symbol_exprt(parameter.get_identifier(), parameter.type()),
            null_pointer_exprt(to_pointer_type(parameter.type()))));
        label_instruction->make_skip();
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
        symbol_table,
        dest);

      function.body.destructive_append(dest);
    }

    if(function.type.return_type() != void_typet())
    {
      auto return_instruction = add_instruction();
      return_instruction->make_return();
      return_instruction->code = code_returnt(side_effect_expr_nondett(
        function.type.return_type(), function_symbol.location));
    }
    auto end_function_instruction = add_instruction();
    end_function_instruction->make_end_function();

    remove_skip(function.body);
  }

private:
  const std::vector<irep_idt> globals_to_havoc;
  std::regex parameters_to_havoc;
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
        params_regex = key_value_pair[1];
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
    return util_make_unique<havoc_generate_function_bodiest>(
      std::move(globals_to_havoc),
      std::move(params_regex),
      object_factory_parameters,
      message_handler);
  }
  throw generate_function_bodies_errort("Can't parse \"" + options + "\"");
}

/// Generate function bodies with some default behavior
/// A list of currently accepted command line arguments
/// + the type of bodies generated by them
///
/// assert-false: { assert(false); }
///
/// assume-false: { assume(false); }
///
/// assert-false-assume-false: {
///   assert(false);
///   assume(false); }
///
/// havoc[,params:regex][,globals:regex]:
/// Assign nondet to the targets of pointer-to-non-const parameters
/// matching regex, and non-const globals matching regex and then
/// return nondet for non-void functions, e.g.:
///
/// int global; const int c_global;
/// int function(int *param, const int *const_param);
///
/// havoc,params:(?!__).*,globals:(?!__).* (where (?!__) means
/// "not preceded by __", which is recommended to avoid overwrite
/// internal symbols), leads to
///
/// int function(int *param, consnt int *const_param) {
///   *param = nondet_int();
///   global = nondet_int();
///   return nondet_int();
/// }
///
/// nondet-return: return nondet for non-void functions
///
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
