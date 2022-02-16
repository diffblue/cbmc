/*******************************************************************\

Module: C Scanner

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "cscanner.h"

cscannert *cscanner_ptr;

int yyclex();
int yyclex_destroy();
void initialize_yyc_scanner();

cscannert::cscannert(std::istream &_in) : in(_in)
{
  initialize_yyc_scanner();
}

cscannert::~cscannert()
{
  yyclex_destroy();
}

ctokent cscannert::operator()()
{
  cscanner_ptr = this;

  if(yyclex() == 0) // EOF
  {
    token.kind = ctokent::END_OF_FILE;
    token.text.clear();
    token.line_number = line_number;
  }

  return std::move(token);
}

std::vector<ctokent> cscannert::get_tokens()
{
  std::vector<ctokent> result;

  do
  {
    result.push_back(this->operator()());
  } while(!is_eof(result.back()));

  return result;
}
