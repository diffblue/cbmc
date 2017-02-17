/*******************************************************************\

Module: Format vector of numbers into a compressed range

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Format vector of numbers into a compressed range

#include <algorithm>
#include <cassert>
#include <string>

#include "format_number_range.h"

/// create shorter representation for output
/// \par parameters: vector of numbers
/// \return string of compressed number range representation
std::string format_number_ranget::operator()(std::vector<unsigned> &numbers)
{
  std::string number_range;
  std::sort(numbers.begin(), numbers.end());
  unsigned end_number=numbers.back();
  if(numbers.front()==end_number)
    number_range=std::to_string(end_number); // only single number
  else
  {
    bool next=true;
    bool first=true;
    bool range=false;
    unsigned start_number=numbers.front();
    unsigned last_number=start_number;

    for(const auto &number : numbers)
    {
      if(next)
      {
        next=false;
        start_number=number;
        last_number=number;
      }
      // advance one forward
      else
      {
        if(number==last_number+1 && !(number==end_number))
        {
          last_number++;
          if(last_number>start_number+1)
            range=true;
        }
        // end this block range
        else
        {
          if(first)
            first=false;
          else
            number_range+=",";
          if(last_number>start_number)
          {
            if(range)
            {
              if(number==end_number && number==last_number+1)
                number_range+=
                  std::to_string(start_number)+"-"+std::to_string(end_number);
              else if(number==end_number)
                number_range+=
                  std::to_string(start_number)+"-"+std::to_string(last_number)+
                  ","+std::to_string(end_number);
              else
                number_range+=
                  std::to_string(start_number)+"-"+std::to_string(last_number);
            }
            else
            {
              if(number!=end_number)
                number_range+=
                  std::to_string(start_number)+","+std::to_string(last_number);
              else
              {
                if(start_number+1==last_number && last_number+1==number)
                  number_range+=
                    std::to_string(start_number)+"-"+std::to_string(end_number);
                else
                  number_range+=
                    std::to_string(start_number)+
                    ","+std::to_string(last_number)+
                    ","+std::to_string(end_number);
              }
            }
            start_number=number;
            last_number=number;
            range=false;
            continue;
          }
          else
          {
            if(number!=end_number)
              number_range+=std::to_string(start_number);
            else
              number_range+=std::to_string(start_number)+","+
                std::to_string(end_number);
            start_number=number;
            last_number=number;
            range=false;
            continue; // already set next start number
          }
          next=true;
        }
      }
    }
  }
  assert(!number_range.empty());
  return number_range;
}
