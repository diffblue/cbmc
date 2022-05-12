/*******************************************************************\

Module: Tests for coverage instrumentation

Author: Diffblue Ltd

\*******************************************************************/

#include <goto-instrument/cover_instrument.h>
#include <testing-utils/use_catch.h>

TEST_CASE("cover_intrument_end_of_function", "[core]")
{
  // Arrange
  goto_programt goto_program{};
  goto_program.add(
    goto_programt::make_function_call(code_function_callt({}, {})));
  goto_program.add(
    goto_programt::make_function_call(code_function_callt({}, {})));
  goto_program.add(goto_programt::make_end_function());
  // Act
  cover_instrument_end_of_function(
    "foo", goto_program, goto_programt::make_assertion);
  // Assert
  REQUIRE(goto_program.instructions.size() == 4);
  const auto newly_inserted = std::next(goto_program.instructions.begin(), 2);
  REQUIRE(newly_inserted->is_assert());
  REQUIRE(newly_inserted->condition() == false_exprt{});
  REQUIRE(newly_inserted->source_location().get_function() == "foo");
}

TEST_CASE("cover_instrument_end_of_function with custom expression", "[core]")
{
  // Arrange
  goto_programt goto_program{};
  goto_program.add(
    goto_programt::make_function_call(code_function_callt({}, {})));
  goto_program.add(
    goto_programt::make_function_call(code_function_callt({}, {})));
  goto_program.add(goto_programt::make_end_function());
  const cover_instrumenter_baset::assertion_factoryt assertion_factory =
    [](const exprt &, const source_locationt &location) {
      return goto_programt::make_assertion(true_exprt{}, location);
    };
  // Act
  cover_instrument_end_of_function("foo", goto_program, assertion_factory);
  // Assert
  REQUIRE(goto_program.instructions.size() == 4);
  const auto newly_inserted = std::next(goto_program.instructions.begin(), 2);
  REQUIRE(newly_inserted->is_assert());
  REQUIRE(newly_inserted->condition() == true_exprt{});
  REQUIRE(newly_inserted->source_location().get_function() == "foo");
}
