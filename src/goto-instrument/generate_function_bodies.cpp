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
    const symbol_tablet &symbol_table,
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
    const symbol_tablet &symbol_table,
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
    const symbol_tablet &symbol_table,
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

class havoc_generate_function_bodiest : public generate_function_bodiest,
                                        private messaget
{
public:
  havoc_generate_function_bodiest(
    std::vector<irep_idt> globals_to_havoc,
    std::regex parameters_to_havoc,
    message_handlert &message_handler)
    : generate_function_bodiest(),
      messaget(message_handler),
      globals_to_havoc(std::move(globals_to_havoc)),
      parameters_to_havoc(std::move(parameters_to_havoc))
  {
  }

private:
  void havoc_expr_rec(
    const exprt &lhs,
    const namespacet &ns,
    const std::function<goto_programt::targett(void)> &add_instruction,
    const irep_idt &function_name) const
  {
    // resolve type symbols
    auto const lhs_type = ns.follow(lhs.type());
    // skip constants
    if(!lhs_type.get_bool(ID_C_constant))
    {
      // expand arrays, structs and union, everything else gets
      // assigned nondet
      if(lhs_type.id() == ID_struct || lhs_type.id() == ID_union)
      {
        // Note: In the case of unions it's often enough to assign
        // just one member; However consider a case like
        // union { struct { const int x; int y; } a;
        //         struct {  int x; const int y; } b;};
        // in this case both a.y and b.x must be assigned
        // otherwise these parts stay constant even though
        // they could've changed (note that type punning through
        // unions is allowed in the C standard but forbidden in C++)
        // so we're assigning all members even in the case of
        // unions just to be safe
        auto const lhs_struct_type = to_struct_union_type(lhs_type);
        for(auto const &component : lhs_struct_type.components())
        {
          havoc_expr_rec(
            member_exprt(lhs, component.get_name(), component.type()),
            ns,
            add_instruction,
            function_name);
        }
      }
      else if(lhs_type.id() == ID_array)
      {
        auto const lhs_array_type = to_array_type(lhs_type);
        if(!lhs_array_type.subtype().get_bool(ID_C_constant))
        {
          bool constant_known_array_size = lhs_array_type.size().is_constant();
          if(!constant_known_array_size)
          {
            warning() << "Cannot havoc non-const array " << format(lhs)
                      << " in function " << function_name
                      << ": Unknown array size" << eom;
          }
          else
          {
            auto const array_size =
              numeric_cast<mp_integer>(lhs_array_type.size());
            INVARIANT(
              array_size.has_value(),
              "Array size should be known constant integer");
            if(array_size.value() == 0)
            {
              // Pretty much the same thing as a unknown size array
              // Technically not allowed by the C standard, but we model
              // unknown size arrays in structs this way
              warning() << "Cannot havoc non-const array " << format(lhs)
                        << " in function " << function_name << ": Array size 0"
                        << eom;
            }
            else
            {
              for(mp_integer i = 0; i < array_size.value(); ++i)
              {
                auto const index =
                  from_integer(i, lhs_array_type.size().type());
                havoc_expr_rec(
                  index_exprt(lhs, index, lhs_array_type.subtype()),
                  ns,
                  add_instruction,
                  function_name);
              }
            }
          }
        }
      }
      else
      {
        auto assign_instruction = add_instruction();
        assign_instruction->make_assignment(
          code_assignt(
            lhs, side_effect_expr_nondett(lhs_type, lhs.source_location())));
      }
    }
  }

protected:
  void generate_function_body_impl(
    goto_functiont &function,
    const symbol_tablet &symbol_table,
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
        std::regex_match(
          id2string(parameter.get_base_name()), parameters_to_havoc))
      {
        // if (param != nullptr) { *param = nondet(); }
        auto goto_instruction = add_instruction();
        havoc_expr_rec(
          dereference_exprt(
            symbol_exprt(parameter.get_identifier(), parameter.type()),
            parameter.type().subtype()),
          ns,
          add_instruction,
          function_name);
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
      havoc_expr_rec(
        symbol_exprt(global_sym.name, global_sym.type),
        ns,
        add_instruction,
        function_name);
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
  const symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(options.empty() || options == "nondet-return")
  {
    return util_make_unique<havoc_generate_function_bodiest>(
      std::vector<irep_idt>{}, std::regex{}, message_handler);
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
      std::move(globals_to_havoc), std::move(params_regex), message_handler);
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
