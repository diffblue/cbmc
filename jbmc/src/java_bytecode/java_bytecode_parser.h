/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSER_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSER_H

#include <iosfwd>
#include <memory>
#include <string>
#include <util/optional.h>

#include "java_type_signature_parser.h"

struct java_bytecodet;
struct java_bytecode_parse_treet;

class java_bytecode_reft
{
private:
  std::unique_ptr<java_bytecodet> bytecode;

public:
  java_bytecode_reft() noexcept;
  explicit java_bytecode_reft(java_bytecodet &&bytecode) noexcept;
  java_bytecode_reft(java_bytecode_reft &&) noexcept;
  ~java_bytecode_reft();

  bool has_value() const
  {
    return bytecode != nullptr;
  }
  java_bytecodet &operator*() const
  {
    return *bytecode;
  }
  optionalt<std::string> get_outer_class_name();
};

/// Attempt to load the bytecode from the given file.
/// \param file: file to load from
/// \param message_handler: handles log messages
/// \param skip_instructions: if true, the loaded class's methods will all be
///   empty. Saves time and memory for consumers that only want signature info.
/// \return parse tree, or empty optionalt on failure
java_bytecode_reft java_bytecode_load(
  const std::string &file,
  class message_handlert &message_handler,
  bool skip_instructions = false);

/// Attempt to load the bytecode from the given stream
/// \param stream: stream to load from
/// \param message_handler: handles log messages
/// \param skip_instructions: if true, the loaded class's methods will all be
///   empty. Saves time and memory for consumers that only want signature info.
/// \return parse tree, or empty optionalt on failure
java_bytecode_reft java_bytecode_load(
  std::istream &stream,
  class message_handlert &message_handler,
  bool skip_instructions = false);

/// Attempt to parse a Java class from the loaded bytecode
/// \param bytecode: the loaded bytecode
/// \param outer_generic_parameters The generic paramaters of the outer class,
///   if any
/// \param message_handler: handles log messages
/// \return parse tree, or empty optionalt on failure
optionalt<java_bytecode_parse_treet> java_bytecode_parse(
  java_bytecode_reft &bytecode,
  const java_generic_type_parameter_mapt &outer_generic_parameters,
  class message_handlert &message_handler);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSER_H
