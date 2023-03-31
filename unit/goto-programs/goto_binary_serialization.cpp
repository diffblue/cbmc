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

TEST_CASE(
  "Test goto_historyt is saved and restored",
  "[core][goto-programs][goto-binary]")
{
  temporary_filet tmp_file{"serialization", ".gb"};

  goto_modelt model{};

  irep_idt foo_name{"foo"};
  auto &foo_function = add_goto_function(foo_name, model);
  foo_function.history.add(goto_transform_kindt::adjust_float_expressions);
  const auto &foo_transforms = foo_function.history.transforms();

  irep_idt bar_name{"bar"};
  auto &bar_function = add_goto_function(bar_name, model);
  bar_function.history.add(goto_transform_kindt::mm_io);
  const auto &bar_transforms = bar_function.history.transforms();

  irep_idt buz_name{"buz"};
  auto &buz_function = add_goto_function(buz_name, model);
  buz_function.history.add(goto_transform_kindt::adjust_float_expressions);
  buz_function.history.add(goto_transform_kindt::mm_io);
  const auto &buz_transforms = buz_function.history.transforms();

  write_goto_binary(tmp_file(), model, null_message_handler);

  auto deserialized_model = read_goto_binary(tmp_file(), null_message_handler);

  REQUIRE(deserialized_model.has_value());
  const auto &deserialized_function_map =
    deserialized_model->goto_functions.function_map;
  REQUIRE(deserialized_function_map.size() == 3);

  const auto deserialized_foo_function =
    deserialized_function_map.find(foo_name);
  REQUIRE(deserialized_foo_function != deserialized_function_map.end());
  REQUIRE(
    deserialized_foo_function->second.history.transforms() == foo_transforms);

  const auto deserialized_bar_function =
    deserialized_function_map.find(bar_name);
  REQUIRE(deserialized_bar_function != deserialized_function_map.end());
  REQUIRE(
    deserialized_bar_function->second.history.transforms() == bar_transforms);

  const auto deserialized_buz_function =
    deserialized_function_map.find(buz_name);
  REQUIRE(deserialized_buz_function != deserialized_function_map.end());
  REQUIRE(
    deserialized_buz_function->second.history.transforms() == buz_transforms);
}
