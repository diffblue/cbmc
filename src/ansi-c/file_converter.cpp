/*******************************************************************\

Module: Convert file contents to C strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Convert file contents to a C character-array initialiser

#include <fstream> // IWYU pragma: keep
#include <iostream>
#include <string>

/// Emit the bytes of \p s as comma-separated character initialisers. Values
/// outside the 7-bit range are cast so the result is valid regardless of
/// whether `char` is signed or unsigned (a brace initialiser would otherwise
/// reject the narrowing conversion).
static void emit_bytes(const std::string &s)
{
  for(const char c : s)
  {
    const unsigned char ch = static_cast<unsigned char>(c);
    if(ch >= 0x80)
      std::cout << "(char)" << unsigned(ch) << ',';
    else
      std::cout << unsigned(ch) << ',';
  }
}

static std::string base_name(const std::string &path)
{
  const std::size_t slash = path.find_last_of("/\\");
  return slash == std::string::npos ? path : path.substr(slash + 1);
}

int main(int argc, char *argv[])
{
  std::string line;

  // Emit a character-array initialiser rather than a string literal: string
  // literals are limited to 65536 characters after concatenation (a limit that
  // clang enforces under -pedantic), whereas a character array has no such
  // limit. The enclosing `{ ... }` is supplied here.
  std::cout << "{";

  for(int i = 1; i < argc; ++i)
  {
    std::ifstream input_file(argv[i]);

    if(!input_file)
    {
      std::cerr << "Failed to open " << argv[i] << '\n';
      return 1;
    }

    // Bake in a #line directive so diagnostics refer to the original header
    // (previously prepended as a separate string literal at the use site).
    emit_bytes("#line 1 \"" + base_name(argv[i]) + "\"\n");

    while(getline(input_file, line))
    {
      if(!line.empty() && line.back() == '\r')
        line.pop_back();
      emit_bytes(line);
      std::cout << "'\\n',";
    }
  }

  // null terminator and closing brace
  std::cout << "0}";

  return 0;
}
