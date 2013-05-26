/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <parser.h>
#include <message_stream.h>
#include <tempfile.h>

#include "javap_parse.h"

class javap_parsert:public parsert
{
public:
  class parsing_errort { };

  virtual bool parse();
 
protected: 
  void rgrammar();
  void rcompiled_from();
  void rclass();
  void rmember();
  
  irep_idt token();
  irep_idt next_token;
};

/*******************************************************************\

Function: javap_parsert::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool javap_parsert::parse()
{
  try
  {
    next_token=0;
    rgrammar();
  }
  
  catch(parsing_errort)
  {
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: javap_parsert::token

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt javap_parsert::token()
{
  if(!next_token.empty())
    return next_token;

  std::string t;
  char ch;

  // skip whitespace
  do
  {
    if(!in->read(&ch, 1)) return "";
  }
  while(ch=='\t' || ch==' ' || ch=='\r' || ch=='\n');

  while(true)
  {
    if(!in->read(&ch, 1)) return t;

    if(isalnum(ch) || ch=='.' || ch=='_')
      t+=ch;
    else if(ch==' ' || ch=='\t' || ch=='\r' || ch=='\n')
      return t;
    else
    {
      next_token=std::string(ch, 1);
      return t;
    }
  }
}

/*******************************************************************\

Function: javap_parsert::rgrammar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rgrammar()
{
  rcompiled_from();

  while(!eof())
    rclass();
}

/*******************************************************************\

Function: javap_parsert::rcompiled_from

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rcompiled_from()
{
  std::string line;
  std::getline(*in, line);
  std::string s="Compiled from \"";
  if(std::string(line, 0, s.size())==s) throw parsing_errort();
  filename=std::string(line, s.size(), line.size()-s.size()-1);
}

/*******************************************************************\

Function: javap_parsert::rmember

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rmember()
{
}

/*******************************************************************\

Function: javap_parsert::rclass

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rclass()
{
  irep_idt t=token();
  
  if(t==ID_public || t==ID_private || t==ID_protected)
  {
    t=token();
  }
  
  if(t!=ID_class) throw parsing_errort();
  
  irep_idt class_id=token();
  
  if(token()!="extends") throw parsing_errort();
  
  irep_idt extends=token();
  
  if(token()!="{") throw parsing_errort();

  while(true)
  {
    irep_idt t=token();
    if(t=="}") break;
    rmember();
  }  
}

/*******************************************************************\

Function: javap_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool javap_parse(
  const std::string &file,
  java_bytecode_parse_treet &parse_tree,
  message_handlert &message_handler)
{
  message_streamt message_stream(message_handler);

  // use javap
  
  std::string stderr_file=get_temporary_file("tmp.stderr", "");
  std::string stdout_file=get_temporary_file("tmp.stdout", "");
  
  std::string command="javap";
  
  command+=" -c -l -private -verbose \""+file+"\"";
  command+=" 2>\""+stderr_file+"\" >\""+stdout_file+"\"";  

  // _popen isn't very reliable on WIN32
  // that's why we use system()
  int result=system(command.c_str());

  std::ifstream stdout_stream(stdout_file.c_str());

  if(!stdout_stream)
  {
    unlink(stdout_file.c_str());
    unlink(stderr_file.c_str());
    message_stream.error("javap failed (open failed)");
    return true;
  }

  javap_parsert javap_parser;
  javap_parser.in=&stdout_stream;  
  
  bool parser_result=javap_parser.parse();

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while((stderr_stream.read(&ch, 1))!=NULL)
      message_stream.str << ch;
  }

  unlink(stdout_file.c_str());
  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.error("javap failed");
    return true;
  }
  else
    message_stream.error_parse(2);  

  return parser_result;
}
