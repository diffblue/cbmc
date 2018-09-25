/*******************************************************************\

Module: Format vector of numbers into a compressed range

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Format vector of numbers into a compressed range

#include <algorithm>
#include <sstream>
#include <string>

#include "invariant.h"

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
