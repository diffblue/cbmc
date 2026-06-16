/*******************************************************************\

Module: Convert file contents to C strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Convert file contents to a C character-array initialiser

#include "file_converter.h"

#include <filesystem>
#include <fstream> // IWYU pragma: keep
#include <iostream>
#include <string>

int main(int argc, char *argv[])
{
  // --line applies to the input files that follow it: the flag is acted upon
  // as argv is scanned left to right, so it must precede those files (the
  // build always passes it first).
  bool line_marker = false;

  // Emit a character-array initialiser rather than a string literal: string
  // literals are limited to 65536 characters after concatenation (a limit
  // clang enforces under -pedantic), whereas a character array has no such
  // limit. The enclosing braces are supplied here.
  std::cout << '{';

  for(int i = 1; i < argc; ++i)
  {
    const std::string arg = argv[i];

    if(arg == "--line")
    {
      line_marker = true;
      continue;
    }

    std::ifstream input_file(arg);

    if(!input_file)
    {
      std::cerr << "Failed to open " << arg << '\n';
      return 1;
    }

    file_converter_append(
      input_file,
      std::cout,
      line_marker,
      std::filesystem::path{arg}.filename().string());
  }

  // null terminator, closing brace and a trailing newline
  std::cout << "0}\n";

  return 0;
}
