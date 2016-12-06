// small unit test for parsing SMT 2 files

#include <cstdlib>

#include <iostream>

#include <solvers/smt2/smt2_parser.h>

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

    // possibly need to quote
    out << buffer;
  }

  virtual void keyword()
  {
    if(first)
      first=false;
    else
      out << ' ';

    out << ':' << buffer;
  }

  virtual void string_literal()
  {
    if(first)
      first=false;
    else
      out << ' ';

    out << '"';

    for(unsigned i=0; i<buffer.size(); i++)
    {
      char ch=buffer[i];
      if(ch=='"') out << '"';
      out << ch;
    }

    out << '"';
  }

  virtual void numeral()
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
    first=false;
  }

  virtual void error(const std::string &message)
  {
    std::cerr << "error: " << message << '\n';
    exit(0);
  }
};

int main()
{
  while(std::cin)
  {
    smt2_parser_testt(std::cin, std::cout)();
    std::cout << '\n';
  }
}
