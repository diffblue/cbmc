/*******************************************************************\

Module: Unit tests for calculate_max_string_length in
        solvers/refinement/string_constraint_generator_valueof.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <solvers/strings/string_constraint_generator.h>
#include <util/std_types.h>

/// Get the string length needed to print any value of the given type with the
/// given radix.
static size_t expected_length(unsigned long radix, const typet &type)
{
  std::string longest("");
  if(radix == 2)
  {
    if(type == unsignedbv_typet(32))
    {
      longest = "11111111111111111111111111111111";
    }
    else if(type == unsignedbv_typet(64))
    {
      longest =
        "1111111111111111111111111111111111111111111111111111111111111111";
    }
    else if(type == signedbv_typet(32))
    {
      longest = "-10000000000000000000000000000000";
    }
    else if(type == signedbv_typet(64))
    {
      longest =
        "-1000000000000000000000000000000000000000000000000000000000000000";
    }
  }
  else if(radix == 8)
  {
    if(type == unsignedbv_typet(32))
    {
      longest = "37777777777";
    }
    else if(type == unsignedbv_typet(64))
    {
      longest = "1777777777777777777777";
    }
    else if(type == signedbv_typet(32))
    {
      longest = "-20000000000";
    }
    else if(type == signedbv_typet(64))
    {
      longest = "-1000000000000000000000";
    }
  }
  else if(radix == 10)
  {
    if(type == unsignedbv_typet(32))
    {
      longest = "4294967295";
    }
    else if(type == unsignedbv_typet(64))
    {
      longest = "18446744073709551615";
    }
    else if(type == signedbv_typet(32))
    {
      longest = "-2147483648";
    }
    else if(type == signedbv_typet(64))
    {
      longest = "-9223372036854775808";
    }
  }
  else if(radix == 16)
  {
    if(type == unsignedbv_typet(32))
    {
      longest = "ffffffff";
    }
    else if(type == unsignedbv_typet(64))
    {
      longest = "ffffffffffffffff";
    }
    else if(type == signedbv_typet(32))
    {
      longest = "-80000000";
    }
    else if(type == signedbv_typet(64))
    {
      longest = "-8000000000000000";
    }
  }

  return longest.size();
}

SCENARIO(
  "calculate_max_string_length",
  "[core][solvers][strings][string_constraint_generator_valueof]")
{
  const unsigned long radixes[] = {2, 8, 10, 16};
  const typet int_types[] = {
    signedbv_typet(32),
    unsignedbv_typet(32),
    signedbv_typet(64),
    unsignedbv_typet(64),
  };

  for(const typet &type : int_types)
  {
    std::string type_str = type.pretty();
    std::replace(type_str.begin(), type_str.end(), '\n', ' ');
    WHEN("type = " + type_str)
    {
      for(const unsigned long radix : radixes)
      {
        WHEN("radix = " + std::to_string(radix))
        {
          size_t actual_value = max_printed_string_length(type, radix);
          THEN("value is correct")
          {
            size_t expected_value = expected_length(radix, type);
            // Due to floating point rounding errors, we sometime get one more
            // than the actual value, which is perfectly fine for our purposes
            // Double brackets here prevent Catch trying to decompose a
            // complex expression
            REQUIRE(
              (actual_value == expected_value ||
               actual_value == expected_value + 1));
          }
          THEN("value is no greater than with default radix")
          {
            size_t actual_value_for_default =
              max_printed_string_length(type, 0);
            REQUIRE(actual_value <= actual_value_for_default);
          }
        }
      }
    }
  }
}
