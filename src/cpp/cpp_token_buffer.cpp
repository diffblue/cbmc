/*******************************************************************\

Module: C++ Parser: Token Buffer

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <assert.h>

#include "cpp_token_buffer.h"
#include "tokens.h"

/*******************************************************************\

Function: cpp_token_buffert::LookAhead

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int cpp_token_buffert::LookAhead(unsigned offset)
{
  assert(current_pos<=token_vector.size());

  offset+=current_pos;

  while(offset>=token_vector.size())
    read_token();

  return token_vector[offset]->kind;
}

/*******************************************************************\

Function: cpp_token_buffert::GetToken

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int cpp_token_buffert::GetToken(cpp_tokent &token)
{
  assert(current_pos<=token_vector.size());

  if(token_vector.size()==current_pos) read_token();

  token=*token_vector[current_pos];

  current_pos++;

  return token.kind;
}

/*******************************************************************\

Function: cpp_token_buffert::GetToken

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int cpp_token_buffert::GetToken()
{
  assert(current_pos<=token_vector.size());

  if(token_vector.size()==current_pos) read_token();
  
  int kind=token_vector[current_pos]->kind;

  current_pos++;

  return kind;
}

/*******************************************************************\

Function: cpp_token_buffert::LookAhead

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int cpp_token_buffert::LookAhead(unsigned offset, cpp_tokent &token)
{
  assert(current_pos<=token_vector.size());

  offset+=current_pos;

  while(offset>=token_vector.size())
    read_token();

  token=*token_vector[offset];

  return token.kind;
}

/*******************************************************************\

Function: cpp_token_buffert::read_token

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int yycpplex();
extern char yycpptext[];

void cpp_token_buffert::read_token()
{
  tokens.push_back(cpp_tokent());
  token_vector.push_back(--tokens.end());

  int kind;

  do
  {
    kind=yycpplex();
  }
  while(kind==Ignore);

  tokens.back().kind=kind;
  tokens.back().pos=token_vector.size()-1;
  //std::cout << "II: " << token_vector.back()->kind << std::endl;
  //std::cout << "I2: " << token_vector.size() << std::endl;
}

/*******************************************************************\

Function: cpp_token_buffert::Save

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_token_buffert::post cpp_token_buffert::Save()
{
  return current_pos;
}

/*******************************************************************\

Function: cpp_token_buffert::Restore

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_token_buffert::Restore(post pos)
{
  current_pos=pos;
}
