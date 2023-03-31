/*******************************************************************\

Module: Unit tests for read_goto_binary and write_goto_binary

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/tempfile.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

goto_functiont &add_goto_function(const irep_idt &name, goto_modelt &model)
{
  goto_functiont function{};
  function.body.add(goto_programt::make_location(source_locationt{}));
  auto result =
    model.goto_functions.function_map.emplace(name, std::move(function));
  return result.first->second;
}

TEST_CASE(
  "Test goto_modelt can be saved and restored",
  "[core][goto-programs][goto-binary]")
{
  temporary_filet tmp_file{"serialization", ".gb"};

  goto_modelt model{};

  irep_idt function_name{"foo"};
  add_goto_function(function_name, model);

  write_goto_binary(tmp_file(), model, null_message_handler);

  auto deserialized_model = read_goto_binary(tmp_file(), null_message_handler);

  REQUIRE(deserialized_model.has_value());
  const auto &deserialized_function_map =
    deserialized_model->goto_functions.function_map;
  REQUIRE(deserialized_function_map.size() == 1);
  REQUIRE(
    deserialized_function_map.find(function_name) !=
    deserialized_function_map.end());
}
