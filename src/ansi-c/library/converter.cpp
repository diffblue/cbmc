/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <string>

bool has_prefix(const std::string &s, const std::string &prefix)
{
  return std::string(s, 0, prefix.size())==prefix;
}

static void convert_line(const std::string &line, bool first)
{
  if(has_prefix(line, "/* FUNCTION: "))
  {
    if(!first)
      std::cout << "},\n";

    std::string function = std::string(line, 13, std::string::npos);
    std::size_t pos = function.find(' ');
    if(pos != std::string::npos)
      function = std::string(function, 0, pos);

    std::cout << "{ \"" << function << "\",\n";
    std::cout << "  \"#line 1 \\\"<builtin-library-" << function
              << ">\\\"\\n\"\n";
  }
  else if(!first)
  {
    std::cout << "  \"";

    for(unsigned i = 0; i < line.size(); i++)
    {
      const char ch = line[i];
      if(ch == '\\')
        std::cout << "\\\\";
      else if(ch == '"')
        std::cout << "\\\"";
      else if(ch == '\r' || ch == '\n')
      {
      }
      else
        std::cout << ch;
    }

    std::cout << "\\n\"\n";
  }
}

int main(int argc, char *argv[])
{
  std::string line;
  bool first = true;

  std::cout << "{\n";

  for(int i = 1; i < argc; ++i)
  {
    std::ifstream input_file(argv[i]);

    if(!input_file)
    {
      std::cerr << "Failed to open " << argv[i] << '\n';
      return 1;
    }

    while(getline(input_file, line))
    {
      convert_line(line, first);
      first = false;
    }
  }

  if(!first)
    std::cout << "},\n";

  std::cout <<
    "{ 0, 0 }\n"
    "}";

  return 0;
}
