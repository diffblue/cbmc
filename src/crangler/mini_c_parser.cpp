/*******************************************************************\

Module: Mini C Parser

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Mini C Parser

#include "mini_c_parser.h"

#include <util/exception_utils.h>
#include <util/invariant.h>

#include "cscanner.h"

class mini_c_parsert
{
public:
  mini_c_parsert()
  {
  }

  c_translation_unitt parse(std::istream &);

protected:
  std::size_t token_index;
  using tokenst = std::vector<ctokent>;
  tokenst tokens;

  bool eof() const
  {
    return is_eof(peek());
  }

  c_declarationt parse_declaration();
  tokenst parse_pre_declarator();
  tokenst parse_declarator();
  tokenst parse_post_declarator();
  tokenst parse_initializer();

  const ctokent &peek() const
  {
    PRECONDITION(token_index < tokens.size());
    return tokens[token_index];
  }

  const ctokent &peek(std::size_t how_many) const
  {
    PRECONDITION(token_index + how_many < tokens.size());
    return tokens[token_index + how_many];
  }

  const ctokent &consume_token()
  {
    PRECONDITION(token_index < tokens.size());
    PRECONDITION(!is_eof(tokens[token_index]));
    return tokens[token_index++];
  }

  static bool is_storage_class(const ctokent &token)
  {
    return token == "auto" || token == "extern" || token == "static" ||
           token == "register" || token == "_Thread_local";
  }

  static bool is_type_qualifier(const ctokent &token)
  {
    return token == "const" || token == "volatile" || token == "restrict" ||
           token == "_Atomic";
  }

  void skip_ws(tokenst &);
  void parse_brackets(char open, char close, tokenst &dest);
};

std::ostream &operator<<(std::ostream &out, const c_declarationt &declaration)
{
  for(const auto &t : declaration.pre_declarator)
    out << t.text;

  for(const auto &t : declaration.declarator)
    out << t.text;

  for(const auto &t : declaration.post_declarator)
    out << t.text;

  for(const auto &t : declaration.initializer)
    out << t.text;

  return out;
}

void c_declarationt::print(std::ostream &out) const
{
  if(!declarator.empty())
  {
    out << "DECLARATOR: ";
    for(const auto &t : declarator)
      out << t.text;
    out << '\n';
  }
}

bool c_declarationt::is_function() const
{
  return !post_declarator.empty() && post_declarator.front() == '(';
}

bool c_declarationt::has_body() const
{
  return !initializer.empty() && initializer.front() == '{';
}

optionalt<ctokent> c_declarationt::declared_identifier() const
{
  for(auto &t : declarator)
    if(is_identifier(t))
      return t;
  return {};
}

void mini_c_parsert::skip_ws(tokenst &dest)
{
  if(eof())
    return;

  while(is_ws(peek()) || is_comment(peek()) ||
        is_preprocessor_directive(peek()))
  {
    dest.push_back(consume_token());
  }
}

void mini_c_parsert::parse_brackets(char open, char close, tokenst &dest)
{
  if(eof() || peek() != open)
    return;

  std::size_t bracket_count = 0;
  while(true)
  {
    if(eof())
      throw invalid_source_file_exceptiont("expected " + std::string(1, close));

    auto &token = consume_token();
    dest.push_back(token);
    if(token == open)
      bracket_count++;
    else if(token == close)
    {
      bracket_count--;
      if(bracket_count == 0)
        break; // done
    }
  }
}

mini_c_parsert::tokenst mini_c_parsert::parse_pre_declarator()
{
  // type qualifier
  // storage class
  // type
  // '*'
  tokenst result;

  while(true)
  {
    skip_ws(result);

    if(eof())
      return result;

    auto &token = peek();

    if(
      is_type_qualifier(token) || is_storage_class(token) || token == '*' ||
      token == "int" || token == "signed" || token.text == "unsigned" ||
      token == "char" || token == "short" || token == "long" ||
      token == "float" || token == "double" || token == "inline" ||
      token == "typedef")
    {
      result.push_back(consume_token());
    }
    else if(token == "enum" || token == "struct" || token == "union")
    {
      result.push_back(consume_token());

      skip_ws(result);

      // may be followed by a tag
      if(!eof() && is_identifier(peek()))
        result.push_back(consume_token());

      skip_ws(result);

      // may be followed by a body {...}
      parse_brackets('{', '}', result);
    }
    else if(token == "__attribute__")
    {
      result.push_back(consume_token());
      skip_ws(result);
      // followed by (( ... ))
      parse_brackets('(', ')', result);
    }
    else if(is_identifier(token))
    {
      // Might be typedef or the declarator.
      // We look ahead for the next non-WS token to tell the difference.
      std::size_t index = 1;
      while(true)
      {
        const auto &next_token = peek(index);
        if(
          is_ws(next_token) || is_preprocessor_directive(next_token) ||
          is_comment(next_token))
          index++;
        else
          break;
      }

      auto &next_token = peek(index);
      if(!is_identifier(next_token) && next_token != '*')
      {
        // 'token' is the declarator
        return result;
      }
      else
        result.push_back(consume_token()); // it's a type
    }
    else if(token == ';')
      return result;
    else if(token == '(') // function type, part of declarator
      return result;
    else
      throw invalid_source_file_exceptiont(
        "expected a declaration but got '" + token.text + "'");
  }
}

mini_c_parsert::tokenst mini_c_parsert::parse_declarator()
{
  // symbol
  // ((...* symbol ...))

  if(eof())
    return {};

  if(peek() == ';')
    return {};

  if(peek() == '(')
  {
    tokenst result;
    parse_brackets('(', ')', result);
    return result;
  }
  else if(is_identifier(peek()))
  {
    return {consume_token()};
  }
  else
    throw invalid_source_file_exceptiont("expected an identifier");
}

mini_c_parsert::tokenst mini_c_parsert::parse_post_declarator()
{
  // consume everything until we see one of the following:
  // 1) ';' (end of declaration)
  // 2) '{' (function body)
  // 3) '=' (initializer)

  tokenst result;

  while(true)
  {
    if(eof())
      return result;

    if(peek() == ';' || peek() == '{' || peek() == '=')
      return result;

    result.push_back(consume_token());
  }
}

mini_c_parsert::tokenst mini_c_parsert::parse_initializer()
{
  if(eof())
    return {};
  else if(peek() == '=')
  {
    tokenst result;
    while(true)
    {
      if(eof())
        throw invalid_source_file_exceptiont("expected an initializer");
      auto &token = consume_token();
      result.push_back(token);
      if(token == ';')
        return result;
    }
  }
  else if(peek() == ';')
  {
    // done
    return {consume_token()};
  }
  else if(peek() == '{')
  {
    // function body
    tokenst result;
    std::size_t bracket_count = 0;
    while(true)
    {
      if(eof())
        throw invalid_source_file_exceptiont("eof in function body");
      auto &token = consume_token();
      result.push_back(token);
      if(token == '{')
        bracket_count++;
      else if(token == '}')
      {
        bracket_count--;
        if(bracket_count == 0)
          return result;
      }
    }
  }
  else
    PRECONDITION(false);
}

c_declarationt mini_c_parsert::parse_declaration()
{
  c_declarationt result;

  result.pre_declarator = parse_pre_declarator();
  result.declarator = parse_declarator();
  result.post_declarator = parse_post_declarator();
  result.initializer = parse_initializer();

  return result;
}

c_translation_unitt mini_c_parsert::parse(std::istream &in)
{
  cscannert cscanner(in);
  cscanner.return_WS_and_comments = true;
  tokens = cscanner.get_tokens();
  token_index = 0;

  if(tokens.empty())
    return {};

  DATA_INVARIANT(is_eof(tokens.back()), "token stream must end on eof");

  c_translation_unitt result;

  while(!eof())
    result.push_back(parse_declaration());

  return result;
}

c_translation_unitt parse_c(std::istream &in)
{
  return mini_c_parsert().parse(in);
}
