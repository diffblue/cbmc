/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ASSEMBLER_ASSEMBLER_PARSER_H
#define CPROVER_ASSEMBLER_ASSEMBLER_PARSER_H

#include <util/parser.h>

#include <list>

class assembler_parsert;
int yyassemblererror(assembler_parsert &, void *, const std::string &error);

class assembler_parsert:public parsert
{
public:
  typedef std::vector<irept> instructiont;
  std::list<instructiont> instructions;

  void add_token(const irept &irep)
  {
    if(instructions.empty())
      new_instruction();

    instructions.back().push_back(irep);
  }

  void new_instruction()
  {
    instructions.push_back(instructiont());
  }

  explicit assembler_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
  }

  bool parse() override;
};

#endif // CPROVER_ASSEMBLER_ASSEMBLER_PARSER_H
