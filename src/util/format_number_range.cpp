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
static void append_numbers(
  const std::string &number_range,
  std::vector<unsigned> &numbers,
  bool last_number_is_set,
  bool is_range)
{
  if(!last_number_is_set && is_range)
  {
    throw deserialization_exceptiont(
      "unterminated number range '" + std::to_string(*(++numbers.rbegin())) +
      "-'");
  }

  if(!last_number_is_set)
  {
    throw deserialization_exceptiont(
      "invalid number range '" + number_range + "'");
  }

  if(is_range)
  {
    unsigned end_range = numbers.back();
    numbers.pop_back();
    unsigned begin_range = numbers.back();
    numbers.pop_back();
    if(begin_range > end_range)
    {
      throw deserialization_exceptiont(
        "lower bound must not be larger than upper bound '" +
        std::to_string(begin_range) + "-" + std::to_string(end_range) + "'");
    }
    for(unsigned i = begin_range; i < end_range; ++i)
      numbers.push_back(i);
    // add upper bound separately to avoid
    // potential overflow issues in the loop above
    numbers.push_back(end_range);
  }
}

std::vector<unsigned> parse_number_range(const std::string &number_range)
{
  std::vector<unsigned> numbers(1, 0);
  bool last_number_is_set = false;
  bool is_range = false;

  for(char c : number_range)
  {
    if('0' <= c && c <= '9')
    {
      numbers.back() *= 10;
      numbers.back() += c - '0';
      last_number_is_set = true;
    }
    else if(c == ',')
    {
      append_numbers(number_range, numbers, last_number_is_set, is_range);

      numbers.push_back(0);
      last_number_is_set = false;
      is_range = false;
    }
    else if(c == '-')
    {
      if(!last_number_is_set)
      {
        throw deserialization_exceptiont(
          "lower bound missing in number range '" + number_range + "'");
      }
      numbers.push_back(0);
      last_number_is_set = false;
      is_range = true;
    }
    else
    {
      throw deserialization_exceptiont(
        std::string("character '") + c + "' not allowed in number range");
    }
  }
  append_numbers(number_range, numbers, last_number_is_set, is_range);

  return numbers;
}
