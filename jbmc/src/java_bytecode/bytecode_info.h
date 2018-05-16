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

typedef uint8_t  u1; // NOLINT(readability/identifiers)
typedef uint16_t u2; // NOLINT(readability/identifiers)
typedef uint32_t u4; // NOLINT(readability/identifiers)
typedef uint64_t u8; // NOLINT(readability/identifiers)
typedef int8_t  s1; // NOLINT(readability/identifiers)
typedef int16_t s2; // NOLINT(readability/identifiers)
typedef int32_t s4; // NOLINT(readability/identifiers)
typedef int64_t s8; // NOLINT(readability/identifiers)

#endif // CPROVER_JAVA_BYTECODE_BYTECODE_INFO_H
