/*******************************************************************\

Module: Unit tests for function_name_manglert

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for function_name_manglert::mangle(), in particular the handling
/// of a mangled name that already exists in the symbol table / function map
/// (regression for #8254).

#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/validation_mode.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/name_mangler.h>

#include <testing-utils/use_catch.h>

#include <string>
#include <vector>

/// The mangled name that the test mangler below always produces.
#define TEST_MANGLED CPROVER_PREFIX "file_local_test_foo"

namespace
{
/// A mangler that ignores its arguments and always returns the same name, so
/// that the test can deterministically create a collision with a pre-existing
/// symbol of that name.
class test_manglert
{
public:
  test_manglert() = default;
  irep_idt operator()(const symbolt &, const std::string &) const
  {
    return TEST_MANGLED;
  }
};

/// A message handler that records all printed messages so the test can assert
/// whether a particular warning was (or was not) emitted.
class recording_message_handlert : public message_handlert
{
public:
  std::vector<std::string> messages;

  void print(unsigned level, const std::string &message) override
  {
    message_handlert::print(level, message);
    messages.push_back(message);
  }

  void print(unsigned, const xmlt &) override
  {
  }

  void print(unsigned, const jsont &) override
  {
  }

  void flush(unsigned) override
  {
  }

  bool contains(const std::string &needle) const
  {
    for(const auto &m : messages)
    {
      if(m.find(needle) != std::string::npos)
        return true;
    }
    return false;
  }
};

/// The type shared by the file-local definition and the forward declaration:
/// `void foo(int)`.
static code_typet make_code_type()
{
  code_typet::parametert param{signed_int_type()};
  param.set_identifier("foo::x");
  return code_typet{{param}, empty_typet{}};
}

/// Add the file-local definition `foo` (symbol with a body) plus its
/// function-map entry (with a body, parameters and function_is_hidden set).
static void add_file_local_definition(goto_modelt &model)
{
  const code_typet code_type = make_code_type();

  symbolt foo_def{"foo", code_type, ID_C};
  foo_def.base_name = "foo";
  foo_def.pretty_name = "foo";
  foo_def.module = "a";
  foo_def.is_file_local = true;
  foo_def.value = code_blockt{}; // non-nil: this is a definition
  model.symbol_table.add(foo_def);

  symbolt param_sym{"foo::x", signed_int_type(), ID_C};
  param_sym.base_name = "x";
  param_sym.module = "a";
  param_sym.is_parameter = true;
  model.symbol_table.add(param_sym);

  goto_functiont foo_fun;
  foo_fun.parameter_identifiers.push_back("foo::x");
  foo_fun.make_hidden();
  foo_fun.body.instructions.emplace_back(
    goto_program_instruction_typet::END_FUNCTION);
  model.goto_functions.function_map.emplace("foo", std::move(foo_fun));
}
} // namespace

SCENARIO(
  "function_name_manglert handles a pre-existing mangled name",
  "[core][goto-programs][name_mangler]")
{
  // A proper architecture is needed so that C types are configured.
  cmdlinet cmdline;
  config.set(cmdline);

  recording_message_handlert message_handler;
  const code_typet code_type = make_code_type();
  const std::string extra_info; // outlives the mangler (it stores a reference)

  GIVEN("a file-local definition whose mangled name is forward-declared")
  {
    goto_modelt model;
    add_file_local_definition(model);

    // Forward declaration of the mangled name: a function symbol with no body
    // and an empty function-map entry, as produced when files are compiled
    // together with --export-file-local-symbols.
    symbolt fwd{TEST_MANGLED, code_type, ID_C};
    fwd.base_name = TEST_MANGLED;
    fwd.module = "main";
    fwd.is_file_local = false; // value stays nil: this is a declaration
    model.symbol_table.add(fwd);
    model.goto_functions.function_map.emplace(TEST_MANGLED, goto_functiont{});

    WHEN("the names are mangled")
    {
      function_name_manglert<test_manglert> mangler{
        message_handler, model, extra_info};
      mangler.mangle();

      THEN("the symbol table stays consistent")
      {
        REQUIRE_NOTHROW(
          model.symbol_table.validate(validation_modet::EXCEPTION));
      }

      THEN("the definition replaces the declaration")
      {
        const symbolt *mangled = model.symbol_table.lookup(TEST_MANGLED);
        REQUIRE(mangled != nullptr);
        REQUIRE_FALSE(mangled->value.is_nil());
        REQUIRE(mangled->type == code_type);
        REQUIRE_FALSE(mangled->is_file_local);
        REQUIRE(model.symbol_table.lookup("foo") == nullptr);
      }

      THEN("the function-map entry carries body, parameters and hidden flag")
      {
        auto entry = model.goto_functions.function_map.find(TEST_MANGLED);
        REQUIRE(entry != model.goto_functions.function_map.end());
        REQUIRE_FALSE(entry->second.body.instructions.empty());
        REQUIRE(
          entry->second.parameter_identifiers ==
          std::vector<irep_idt>{"foo::x"});
        REQUIRE(entry->second.is_hidden());
        REQUIRE(
          model.goto_functions.function_map.find("foo") ==
          model.goto_functions.function_map.end());
      }

      THEN("no 'already exists with a definition' warning is emitted")
      {
        REQUIRE_FALSE(
          message_handler.contains("already exists with a definition"));
      }
    }
  }

  GIVEN("a file-local definition whose mangled name already has a definition")
  {
    goto_modelt model;
    add_file_local_definition(model);

    // The mangled name already denotes a full definition (non-nil value).
    symbolt existing{TEST_MANGLED, code_type, ID_C};
    existing.base_name = TEST_MANGLED;
    existing.module = "main";
    existing.is_file_local = false;
    existing.value = code_skipt{}; // distinguishable, non-nil definition
    model.symbol_table.add(existing);
    goto_functiont existing_fun;
    existing_fun.body.instructions.emplace_back(
      goto_program_instruction_typet::END_FUNCTION);
    model.goto_functions.function_map.emplace(
      TEST_MANGLED, std::move(existing_fun));

    WHEN("the names are mangled")
    {
      function_name_manglert<test_manglert> mangler{
        message_handler, model, extra_info};
      mangler.mangle();

      THEN("a warning is emitted and the existing definition is preserved")
      {
        REQUIRE(message_handler.contains("already exists with a definition"));
        const symbolt *mangled = model.symbol_table.lookup(TEST_MANGLED);
        REQUIRE(mangled != nullptr);
        REQUIRE(mangled->value == code_skipt{});
        REQUIRE_NOTHROW(
          model.symbol_table.validate(validation_modet::EXCEPTION));
      }
    }
  }

  GIVEN("a file-local definition whose mangled name is a non-function symbol")
  {
    goto_modelt model;
    add_file_local_definition(model);

    // A non-function symbol happens to share the mangled name. It must not be
    // overwritten just because its value is nil.
    symbolt var{TEST_MANGLED, signed_int_type(), ID_C};
    var.base_name = TEST_MANGLED;
    var.module = "main";
    model.symbol_table.add(var);

    WHEN("the names are mangled")
    {
      function_name_manglert<test_manglert> mangler{
        message_handler, model, extra_info};
      mangler.mangle();

      THEN("the non-function symbol is left untouched and a warning is emitted")
      {
        REQUIRE(message_handler.contains("already exists with a definition"));
        const symbolt *mangled = model.symbol_table.lookup(TEST_MANGLED);
        REQUIRE(mangled != nullptr);
        REQUIRE(mangled->type == signed_int_type());
        REQUIRE_NOTHROW(
          model.symbol_table.validate(validation_modet::EXCEPTION));
      }
    }
  }
}
