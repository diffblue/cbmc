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

struct bytecode_infot
{
  const char *mnemonic;
  unsigned char opcode;
  unsigned pop, push;
  char result_type;
};

extern struct bytecode_infot const bytecode_info[];

