/*******************************************************************\

Module: Format specifiers for String.format

Author: Romain Brenguier, Joel Allred

\*******************************************************************/

/// \file
///  Format specifiers for String.format

#ifndef CPROVER_SOLVERS_STRINGS_FORMAT_SPECIFIER_H
#define CPROVER_SOLVERS_STRINGS_FORMAT_SPECIFIER_H

#include <string>
#include <util/invariant.h>
#include <vector>

// Format specifier describes how a value should be printed.
/// Field names follow the OpenJDK implementation:
/// http://hg.openjdk.java.net/jdk7/jdk7/jdk/file/9b8c96f96a0f/src/share/classes/java/util/Formatter.java#l2569
class format_specifiert
{
public:
  // Constants describing the meaning of characters in format specifiers.
  static const char DECIMAL_INTEGER = 'd';
  static const char OCTAL_INTEGER = 'o';
  static const char HEXADECIMAL_INTEGER = 'x';
  static const char HEXADECIMAL_INTEGER_UPPER = 'X';
  static const char SCIENTIFIC = 'e';
  static const char SCIENTIFIC_UPPER = 'E';
  static const char GENERAL = 'g';
  static const char GENERAL_UPPER = 'G';
  static const char DECIMAL_FLOAT = 'f';
  static const char HEXADECIMAL_FLOAT = 'a';
  static const char HEXADECIMAL_FLOAT_UPPER = 'A';
  static const char CHARACTER = 'c';
  static const char CHARACTER_UPPER = 'C';
  static const char DATE_TIME = 't';
  static const char DATE_TIME_UPPER = 'T';
  static const char BOOLEAN = 'b';
  static const char BOOLEAN_UPPER = 'B';
  static const char STRING = 's';
  static const char STRING_UPPER = 'S';
  static const char HASHCODE = 'h';
  static const char HASHCODE_UPPER = 'H';
  static const char LINE_SEPARATOR = 'n';
  static const char PERCENT_SIGN = '%';

  int index = -1;
  std::string flag;
  int width;
  int precision;
  // date/time
  bool dt = false;
  char conversion;

  format_specifiert(
    int _index,
    std::string _flag,
    int _width,
    int _precision,
    bool _dt,
    char conversion)
    : index(_index),
      flag(_flag),
      width(_width),
      precision(_precision),
      dt(_dt),
      conversion(conversion)
  {
  }
};

// Format text represent a constant part of a format string.
class format_textt
{
public:
  format_textt() = default;

  explicit format_textt(std::string _content) : content(_content)
  {
  }

  format_textt(const format_textt &fs) : content(fs.content)
  {
  }

  std::string get_content() const
  {
    return content;
  }

private:
  std::string content;
};

// A format element is either a specifier or text.
class format_elementt
{
public:
  typedef enum
  {
    SPECIFIER,
    TEXT
  } format_typet;

  explicit format_elementt(format_typet _type) : type(_type)
  {
  }

  explicit format_elementt(std::string s) : type(TEXT), fstring(s)
  {
  }

  explicit format_elementt(format_specifiert fs) : type(SPECIFIER)
  {
    fspec.push_back(fs);
  }

  bool is_format_specifier() const
  {
    return type == SPECIFIER;
  }

  bool is_format_text() const
  {
    return type == TEXT;
  }

  format_specifiert get_format_specifier() const
  {
    PRECONDITION(is_format_specifier());
    return fspec.back();
  }

  format_textt &get_format_text()
  {
    PRECONDITION(is_format_text());
    return fstring;
  }

  const format_textt &get_format_text() const
  {
    PRECONDITION(is_format_text());
    return fstring;
  }

private:
  format_typet type;
  format_textt fstring;
  std::vector<format_specifiert> fspec;
};

/// Parse the given string into format specifiers and text.
/// This follows the implementation in openJDK of the java.util.Formatter class:
/// http://hg.openjdk.java.net/jdk7/jdk7/jdk/file/9b8c96f96a0f/src/share/classes/java/util/Formatter.java#l2513
/// \param s: a string
/// \return A vector of format_elementt.
std::vector<format_elementt> parse_format_string(std::string s);

#endif // CPROVER_SOLVERS_STRINGS_FORMAT_SPECIFIER_H
