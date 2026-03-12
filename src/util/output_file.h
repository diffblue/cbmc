/*******************************************************************\

Module: Output File Container

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_UTIL_OUTPUT_FILE_H
#define CPROVER_UTIL_OUTPUT_FILE_H

/// \file
/// Output file container that handles stdout ("-") and regular files

#include <iosfwd>
#include <memory>
#include <string>

/// RAII container for an output stream that is either stdout or a file.
/// Pass "-" as the file name to write to stdout.
class output_filet final
{
public:
  /// Create a stream to the given file name, or stdout if "-".
  /// Throws system_exceptiont if the file cannot be opened.
  explicit output_filet(std::string file_name);
  ~output_filet();

  std::ostream &stream()
  {
    return *_stream;
  }

  /// The name of the file, or "stdout".
  const std::string &name() const
  {
    return _name;
  }

  /// True if the output is a file (not stdout).
  bool is_file() const
  {
    return _ofstream != nullptr;
  }

private:
  std::string _name;
  std::unique_ptr<std::ofstream> _ofstream;
  std::ostream *_stream = nullptr;
};

#endif // CPROVER_UTIL_OUTPUT_FILE_H
