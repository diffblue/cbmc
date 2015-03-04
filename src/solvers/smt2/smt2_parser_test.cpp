// small unit test for parsing SMT 2 files

#include <iostream>

#include "smt2_parser.h"

/*******************************************************************\

Function: smt2_parser_test

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class smt2_parser_testt:public smt2_parsert
{
public:
  smt2_parser_testt(std::istream &_in, std::ostream &_out):
    smt2_parsert(_in), out(_out), first(true)
  {
  }
  
protected:
  std::ostream &out;
  bool first;

  // overload from smt2_parsert

  virtual void symbol()
  {
    if(first)
      first=false;
    else
      out << ' ';

    out << buffer;
  }
  
  virtual void open_expression() // '('
  {
    if(!first)
      out << ' ';
      
    out << '(';
    first=true;
  }
  
  virtual void close_expression() // ')'
  {
    out << ')';
  }
};

int main()
{
  smt2_parser_testt(std::cin, std::cout)();
}
