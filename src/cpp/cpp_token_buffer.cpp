/*******************************************************************\

Module: C++ Parser: Token Buffer

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser: Token Buffer

#include "cpp_token_buffer.h"

#include <ansi-c/ansi_c_parser.h>

int cpp_token_buffert::LookAhead(unsigned offset)
{
  assert(current_pos<=token_vector.size());

  offset+=current_pos;

  while(offset>=token_vector.size())
    read_token();

  return token_vector[offset]->kind;
}

int cpp_token_buffert::get_token(cpp_tokent &token)
{
  assert(current_pos<=token_vector.size());

  if(token_vector.size()==current_pos)
    read_token();

  token=*token_vector[current_pos];

  current_pos++;

  return token.kind;
}

int cpp_token_buffert::get_token()
{
  assert(current_pos<=token_vector.size());

  if(token_vector.size()==current_pos)
    read_token();

  int kind=token_vector[current_pos]->kind;

  current_pos++;

  return kind;
}

int cpp_token_buffert::LookAhead(unsigned offset, cpp_tokent &token)
{
  assert(current_pos<=token_vector.size());

  offset+=current_pos;

  while(offset>=token_vector.size())
    read_token();

  token=*token_vector[offset];

  return token.kind;
}

int yyansi_clex();
extern char *yyansi_ctext;

void cpp_token_buffert::read_token()
{
  tokens.push_back(cpp_tokent());
  token_vector.push_back(--tokens.end());

  int kind;

  ansi_c_parser.stack.clear();
  kind=yyansi_clex();
  tokens.back().text=yyansi_ctext;
  if(ansi_c_parser.stack.size()==1)
  {
    tokens.back().data=ansi_c_parser.stack.front();
    tokens.back().line_no=ansi_c_parser.get_line_no();
    tokens.back().filename=ansi_c_parser.get_file();
  }

  // std::cout << "TOKEN: " << kind << " " << tokens.back().text << '\n';

  tokens.back().kind=kind;

  // std::cout << "II: " << token_vector.back()->kind << '\n';
  // std::cout << "I2: " << token_vector.size() << '\n';
}

cpp_token_buffert::post cpp_token_buffert::Save()
{
  return current_pos;
}

void cpp_token_buffert::Restore(post pos)
{
  current_pos=pos;
}

void cpp_token_buffert::Replace(const cpp_tokent &token)
{
  assert(current_pos<=token_vector.size());

  if(token_vector.size()==current_pos)
    read_token();

  *token_vector[current_pos]=token;
}

void cpp_token_buffert::Insert(const cpp_tokent &token)
{
  assert(current_pos<=token_vector.size());

  tokens.push_back(token);

  token_vector.insert(token_vector.begin()+current_pos,
                      --tokens.end());
}
