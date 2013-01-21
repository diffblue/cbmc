/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ASSEMBLER_PARSER_H
#define CPROVER_ASSEMBLER_PARSER_H

#include <parser.h>
#include <expr.h>

int yyassemblerlex();
int yyassemblererror(const std::string &error);
void assembler_scanner_init();

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
  
  assembler_parsert()
  {
  }
  
  virtual bool parse()
  {
    yyassemblerlex();
    return false;
  }

  virtual void clear()
  {
    parsert::clear();
    instructions.clear();
    //assembler_scanner_init();
  }
};

extern assembler_parsert assembler_parser;

#endif
