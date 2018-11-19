/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSER_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSER_H

#include <iosfwd>
#include <string>
#include <util/optional.h>

struct java_bytecode_parse_treet;

/// Attempt to parse a Java class from the given file.
/// \param file: file to load from
/// \param msg: handles log messages
/// \param skip_instructions: if true, the loaded class's methods will all be
///   empty. Saves time and memory for consumers that only want signature info.
/// \return parse tree, or empty optionalt on failure
optionalt<java_bytecode_parse_treet>
java_bytecode_parse(
  const std::string &file,
  class message_handlert &msg,
  bool skip_instructions = false);

/// Attempt to parse a Java class from the given stream
/// \param stream: stream to load from
/// \param msg: handles log messages
/// \param skip_instructions: if true, the loaded class's methods will all be
///   empty. Saves time and memory for consumers that only want signature info.
/// \return parse tree, or empty optionalt on failure
optionalt<java_bytecode_parse_treet>
java_bytecode_parse(
  std::istream &stream,
  class message_handlert &msg,
  bool skip_instructions = false);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSER_H
