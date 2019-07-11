/*******************************************************************\

Module: Rust Language Conversion

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/

/// \file
/// Rust Language Conversion
#define yyFlexLexer yyrustFlexLexer
#include <FlexLexer.h>
#include <util/std_expr.h>

#include <string>
#include <vector>

#include "rust_parseassert.h"

void TokenTreeToString(
  std::stringstream &string,
  multi_ary_exprt const &tokenTree)
{
  for(auto &token : tokenTree.operands())
  {
    if(token.has_operands())
    {
      TokenTreeToString(string, to_multi_ary_expr(token));
    }
    else if(token.id() == ID_symbol)
    {
      string << to_symbol_expr(token).get_identifier() << " ";
    }
  }
}

extern void
UseDifferentScanner(yyFlexLexer *newScanner, std::istream &newInStream);
extern void PopToPreviousScanner();

exprt parse_token_tree(multi_ary_exprt const &tokenTree)
{
  // add enough to make it valid parsible code
  std::stringstream tokenTreeStream;
  tokenTreeStream << "fn fakeFunction() { ";
  TokenTreeToString(tokenTreeStream, tokenTree);
  tokenTreeStream << "; }";
  std::stringstream outputStream;

  yyFlexLexer tokTreeScanner(&tokenTreeStream, &outputStream);
  // use the scanner made for this stream
  UseDifferentScanner(&tokTreeScanner, tokenTreeStream);

  yyrust::parser tokTreeParser;
  std::istream *oldStream = rust_parser.in;
  // TODO Once line numbers are being used, undo the line increase that
  //       happens because of the read function on rust_parser
  rust_parser.in = &tokenTreeStream;
  // TODO Debug Turn off debug output
  // tokTreeParser.set_debug_level(1);

  int parseResult = tokTreeParser.parse();
  rust_parser.in = oldStream;
  // if parsing succeeds
  if(parseResult == 0)
  {
    // reset to default scanning to resume parsing the original file(s)
    PopToPreviousScanner();

    // get the parse tree
    rust_declarationt parseTree = rust_parser.parse_tree.items.back();
    // clear it from the list
    rust_parser.parse_tree.items.pop_back();

    // strip the added code
    exprt boolExpression = parseTree.value().operands()[0].operands()[0];
    return boolExpression;
  }
  else
  {
    // reset to default scanning to resume parsing the original file(s)
    PopToPreviousScanner();
    return exprt();
  }
}
