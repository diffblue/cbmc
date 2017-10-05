/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_BYTECODE_INFO_H
#define CPROVER_JAVA_BYTECODE_BYTECODE_INFO_H

#include <cstdint>

// http://en.wikipedia.org/wiki/Java_bytecode_instruction_listings

// The 'result_type' is one of the following:
// i  integer
// l  long
// s  short
// b  byte
// c  character
// f  float
// d  double
// z  boolean
// a  reference

// The 'format' is:
// ' ' - just one byte
// 'c' - a constant_pool index, one byte
// 'C' - a constant_pool index, two bytes
// 'b' - a byte, signed
// 'o' - two byte branch offset
// 'O' - four byte branch offset
// 'v' - local variable index, one byte
// 'V' - local variable index, one byte, plus one byte, signed
// 'I' - two byte constant_pool index, plus two bytes
// 'L' - lookupswitch
// 'T' - tableswitch
// 'm' - multianewarray
// 't' - array subtype, one byte
// 's' - a short, signed

struct bytecode_infot
{
  const char *mnemonic;
  unsigned char opcode;
  char format;
  unsigned pop, push;
  char result_type;
};

extern struct bytecode_infot const bytecode_info[];

using u1 = uint8_t ; // NOLINT(readability/identifiers)
using u2 = uint16_t; // NOLINT(readability/identifiers)
using u4 = uint32_t; // NOLINT(readability/identifiers)
using u8 = uint64_t; // NOLINT(readability/identifiers)
using s1 = int8_t ; // NOLINT(readability/identifiers)
using s2 = int16_t; // NOLINT(readability/identifiers)
using s4 = int32_t; // NOLINT(readability/identifiers)
using s8 = int64_t; // NOLINT(readability/identifiers)

#endif // CPROVER_JAVA_BYTECODE_BYTECODE_INFO_H
