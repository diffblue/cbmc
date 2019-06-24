/*******************************************************************\

Module: Format vector of numbers into a compressed range

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Format vector of numbers into a compressed range

#include <algorithm>
#include <sstream>
#include <string>

#include "exception_utils.h"
#include "invariant.h"
#include "optional.h"

#include "format_number_range.h"

/// create shorter representation for output
/// \param input_numbers: vector of numbers
/// \return string of compressed number range representation
std::string format_number_range(const std::vector<unsigned> &input_numbers)
{
  PRECONDITION(!input_numbers.empty());

  std::vector<unsigned> numbers(input_numbers);
  std::sort(numbers.begin(), numbers.end());
  unsigned end_number=numbers.back();
  if(numbers.front()==end_number)
    return std::to_string(end_number); // only single number

  std::stringstream number_range;

  auto start_number = numbers.front();

  for(std::vector<unsigned>::const_iterator it = numbers.begin();
      it != numbers.end();
      ++it)
  {
    const auto number = *it;
    const auto next = std::next(it);

    // advance one forward
    if(next != numbers.end() && *next <= number + 1)
      continue;

    // end this block range
    if(start_number != numbers.front())
      number_range << ',';

    if(number == start_number)
    {
      number_range << number;
    }
    else if(number == start_number + 1)
    {
      number_range << start_number << ',' << number;
    }
    else
    {
      number_range << start_number << '-' << number;
    }

    if(next != numbers.end())
      start_number = *next;
  }

  POSTCONDITION(!number_range.str().empty());
  return number_range.str();
}

/// Appends \p number resp. numbers \p begin_range ... \p number to \p numbers
static void append_numbers_and_reset(
  const std::string &number_range,
  std::vector<unsigned> &numbers,
  optionalt<unsigned> &begin_range,
  optionalt<unsigned> &number)
{
  if(!number.has_value() && begin_range.has_value())
  {
    throw deserialization_exceptiont(
      "unterminated number range '" + std::to_string(*begin_range) + "-'");
  }

  if(!number.has_value())
  {
    throw deserialization_exceptiont(
      "invalid number range '" + number_range + "'");
  }

  if(number.has_value() && begin_range.has_value())
  {
    if(*begin_range > *number)
    {
      throw deserialization_exceptiont(
        "lower bound must not be larger than upper bound '" +
        std::to_string(*begin_range) + "-" + std::to_string(*number) + "'");
    }
    for(unsigned i = *begin_range; i < *number; ++i)
      numbers.push_back(i);
    // add upper bound separately to avoid
    // potential overflow issues in the loop above
    numbers.push_back(*number);
    begin_range = {};
    number = {};
  }
  else if(number.has_value() && !begin_range.has_value())
  {
    numbers.push_back(*number);
    number = {};
  }
}

std::vector<unsigned> parse_number_range(const std::string &number_range)
{
  std::vector<unsigned> numbers;

  optionalt<unsigned> begin_range;
  optionalt<unsigned> number;
  for(char c : number_range)
  {
    if('0' <= c && c <= '9')
    {
      if(!number.has_value())
        number = 0;
      *number = 10 * *number + (c - '0');
    }
    else if(c == ',')
    {
      append_numbers_and_reset(number_range, numbers, begin_range, number);
    }
    else if(c == '-')
    {
      if(!number.has_value())
      {
        throw deserialization_exceptiont(
          "lower bound missing in number range '" + number_range + "'");
      }
      begin_range = number;
      number = {};
    }
    else
    {
      throw deserialization_exceptiont(
        std::string("character '") + c + "' not allowed in number range");
    }
  }
  append_numbers_and_reset(number_range, numbers, begin_range, number);

  return numbers;
}
