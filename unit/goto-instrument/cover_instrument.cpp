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
  goto_program.add(goto_programt::make_return());
  // Act
  cover_instrument_end_of_function("foo", goto_program);
  // Assert
  REQUIRE(goto_program.instructions.size() == 4);
  const auto newly_inserted = std::next(goto_program.instructions.begin(), 2);
  REQUIRE(newly_inserted->is_assert());
  REQUIRE(newly_inserted->source_location.get_function() == "foo");
}
