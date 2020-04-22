/*******************************************************************\

Module: Convert file contents to C strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Convert file contents to C strings

#include <fstream>
#include <iostream>
#include <string>

static void convert_line(const std::string &line)
{
  std::cout << "\"";

  for(std::size_t i = 0; i < line.size(); i++)
  {
    const char ch = line[i];
    if(ch == '\\')
      std::cout << "\\\\";
    else if(ch == '"')
      std::cout << "\\\"";
    else if(ch == '\r' || ch == '\n')
    {
    }
    else if((ch & 0x80) != 0)
    {
      std::cout << "\\x" << std::hex << (unsigned(ch) & 0xff) << std::dec;
    }
    else
      std::cout << ch;
  }

  std::cout << "\\n\"\n";
}

int main(int argc, char *argv[])
{
  std::string line;

  for(int i = 1; i < argc; ++i)
  {
    std::ifstream input_file(argv[i]);

    if(!input_file)
    {
      std::cerr << "Failed to open " << argv[i] << '\n';
      return 1;
    }

    while(getline(input_file, line))
      convert_line(line);
  }

  return 0;
}
