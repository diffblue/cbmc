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

optionalt<java_bytecode_parse_treet>
java_bytecode_parse(const std::string &file, class message_handlert &);

optionalt<java_bytecode_parse_treet>
java_bytecode_parse(std::istream &, class message_handlert &);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSER_H
