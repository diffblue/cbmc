// Copyright 2016-2020 Diffblue Limited. All Rights Reserved.

#include <goto-checker/report_util.cpp>
#include <testing-utils/use_catch.h>

static goto_programt::instructiont instruction_for_location(
  const irep_idt &file,
  const irep_idt &function,
  size_t line_no)
{
  source_locationt location;
  location.set_file(file);
  location.set_function(function);
  location.set_line(line_no);
  goto_programt::instructiont instruction;
  instruction.source_location_nonconst() = location;
  return instruction;
}

static property_infot test_info(const goto_programt::const_targett &target)
{
  return property_infot(target, "ignored", property_statust::UNKNOWN);
}

static propertyt
property(const irep_idt &identifier, const property_infot &info)
{
  return std::make_pair(identifier, info);
}

std::ostream &operator<<(std::ostream &os, const propertyt &value)
{
  os << "{ property_id=" << value.first << ", "
     << " property_location={ "
     << " file=" << value.second.pc->source_location().get_file() << ", "
     << " function=" << value.second.pc->source_location().get_function()
     << ", "
     << " line=" << value.second.pc->source_location().get_line() << "}}";
  return os;
}

TEST_CASE("Comparing two properties", "[core][goto-checker][report_util]")
{
  SECTION("Compare locations")
  {
    goto_programt::instructionst instructions;
    instructions.push_back(instruction_for_location("fileA", "funcA", 1));
    instructions.push_back(instruction_for_location("fileA", "funcA", 2));
    instructions.push_back(instruction_for_location("fileA", "funcB", 1));
    instructions.push_back(instruction_for_location("fileA", "funcB", 2));
    instructions.push_back(instruction_for_location("fileB", "funcA", 1));
    instructions.push_back(instruction_for_location("fileB", "funcA", 2));
    instructions.push_back(instruction_for_location("fileB", "funcB", 1));
    instructions.push_back(instruction_for_location("fileB", "funcB", 2));

    for(auto first_location = instructions.begin();
        first_location != instructions.end();
        ++first_location)
    {
      for(auto second_location = std::next(first_location);
          second_location != instructions.end();
          ++second_location)
      {
        const propertyt p1 = property("ignored", test_info(first_location));
        const propertyt p2 = property("ignored", test_info(second_location));
        INFO(p1);
        INFO(p2);
        REQUIRE(is_property_less_than(p1, p2));
        REQUIRE_FALSE(is_property_less_than(p2, p1));
      }
    }
  }
  SECTION("Compare property ids")
  {
    goto_programt::instructionst instructions;
    instructions.push_back(instruction_for_location("fileA", "funcA", 1));

    std::vector<irep_idt> properties;
    properties.push_back("A.1");
    properties.push_back("A.2");
    properties.push_back("B.1");
    properties.push_back("B.2");

    for(auto first_property = properties.begin();
        first_property != properties.end();
        ++first_property)
    {
      for(auto second_property = std::next(first_property);
          second_property != properties.end();
          ++second_property)
      {
        const propertyt p1 =
          property(*first_property, test_info(instructions.begin()));
        const propertyt p2 =
          property(*second_property, test_info(instructions.begin()));
        INFO(p1);
        INFO(p2);
        REQUIRE(is_property_less_than(p1, p2));
        REQUIRE_FALSE(is_property_less_than(p2, p1));
      }
    }
  }
}
