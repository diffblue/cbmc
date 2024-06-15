/*******************************************************************\

Module: Convert file contents to a C array

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Convert file contents to a C array

#include <fstream> // IWYU pragma: keep
#include <iomanip>
#include <iostream>
#include <string>

int main(int argc, char *argv[])
{
  std::size_t counter = 0;
  bool first = true;

  std::cout << "{";

  for(int i = 1; i < argc; ++i)
  {
    std::ifstream input_file(argv[i]);

    if(!input_file)
    {
      std::cerr << "Failed to open " << argv[i] << '\n';
      return 1;
    }

    char ch;
    while(input_file.get(ch))
    {
      if(first)
        first = false;
      else
        std::cout << ',';

      if(counter == 15)
      {
        std::cout << '\n';
        counter = 0;
      }
      else
      {
        counter++;
        std::cout << ' ';
      }

      std::cout << "0x" << std::hex << std::setw(2) << std::setfill('0')
                << int(ch);
    }
  }

  std::cout << " }\n";

  return 0;
}
