/*******************************************************************\

Module: Convert file contents to C strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Convert file contents to a C character-array initialiser

#ifndef CPROVER_ANSI_C_FILE_CONVERTER_H
#define CPROVER_ANSI_C_FILE_CONVERTER_H

#include <istream>
#include <string>

/// Emit the bytes of \p s to \p out as comma-separated decimal byte values
/// (not character literals). A byte with the high bit set is written with a
/// `(char)` cast so the surrounding braced initialiser is valid regardless of
/// whether `char` is signed or unsigned -- a brace initialiser would otherwise
/// reject the narrowing conversion of a value > 127.
inline void file_converter_emit_bytes(std::ostream &out, const std::string &s)
{
  for(const char c : s)
  {
    const unsigned char ch = static_cast<unsigned char>(c);
    if(ch >= 0x80)
      out << "(char)" << unsigned(ch) << ',';
    else
      out << unsigned(ch) << ',';
  }
}

/// Append the contents of \p in to \p out as the body of a C character-array
/// initialiser; the enclosing braces and trailing null terminator are supplied
/// by the caller. Each input line contributes its bytes followed by a newline
/// byte (the sole character literal emitted) and a physical line break, so one
/// output line corresponds to one input line -- this keeps the generated
/// initialiser diffable and within compiler line-length limits. When
/// \p line_marker is set, a `#line` directive naming \p file_name is emitted
/// first so that diagnostics refer to the original file.
inline void file_converter_append(
  std::istream &in,
  std::ostream &out,
  bool line_marker,
  const std::string &file_name)
{
  if(line_marker)
  {
    file_converter_emit_bytes(out, "#line 1 \"" + file_name + "\"\n");
    out << '\n';
  }

  std::string line;
  while(std::getline(in, line))
  {
    if(!line.empty() && line.back() == '\r')
      line.pop_back();
    file_converter_emit_bytes(out, line);
    out << "'\\n',\n";
  }
}

#endif // CPROVER_ANSI_C_FILE_CONVERTER_H
