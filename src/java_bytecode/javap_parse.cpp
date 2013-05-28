/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>

#include <util/parser.h>
#include <util/message_stream.h>
#include <util/tempfile.h>
#include <util/suffix.h>
#include <util/prefix.h>

#include "javap_parse.h"

#ifdef __linux__
#include <unistd.h>
#endif

#ifdef __FreeBSD_kernel__
#include <unistd.h>
#endif

#ifdef __GNU__
#include <unistd.h>
#endif

#ifdef __MACH__
#include <unistd.h>
#endif

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

class javap_parsert:public parsert
{
public:
  class parsing_errort
  { 
  public:
    explicit inline parsing_errort(const char *_msg):msg(_msg)
    {
    }
    
    const char *msg;
  };

  virtual bool parse();
  
  typedef java_bytecode_parse_treet::itemt itemt;
 
protected: 
  void rgrammar();
  void rcompiled_from();
  void rclass();
  void rmembers();
  void rconstant(const std::string &line);

  inline std::string getline()
  {
    std::string line;
    std::getline(*in, line);
    return line;
  }
  
  bool skip(const std::string &what, std::string &where)
  {
    if(std::string(where, 0, what.size())==what)
    {
      where=std::string(where, what.size(), std::string::npos);
      return false;
    }
    else
      return true;
  }
  
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
    next_token=irep_idt();
    rgrammar();
  }
  
  catch(const parsing_errort &p)
  {
    error(p.msg);
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
  std::string t;

  // do we have one buffered?

  if(!next_token.empty())
  {
    irep_idt tmp=next_token;
    next_token=irep_idt();
    return tmp;
  }
  
  // get a new token

  char ch;

  while(1)
  {
    if(!in->read(&ch, 1))
      return t;

    if(isalnum(ch) || ch=='.' || ch=='_' || ch=='$')
      t+=ch;
    else if(ch==' ' || ch=='\t' || ch=='\r' || ch=='\n')
    {
      // whitespace
      if(t!="") return t;
    }
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
  if(std::string(line, 0, s.size())!=s)
    throw parsing_errort("Expected 'Compiled from'");
  filename=std::string(line, s.size(), line.size()-s.size()-1);
}

/*******************************************************************\

Function: javap_parsert::rconstant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rconstant(const std::string &line)
{
  // #1 = Method	#6.#15;
//  parse_tree.add();
}
  
/*******************************************************************\

Function: javap_parsert::rmembers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rmembers()
{
  std::string line;
  
  while(!eof())
  {
    line=getline();
    
    #ifdef DEBUG
    std::cout << "rmembers *** " << line << std::endl;
    #endif

    if(has_prefix(line, "   line "))
    {
    }
    else if(line=="}")
    {
      return;
    }
  }
}

/*******************************************************************\

Function: javap_parsert::rclass

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rclass()
{
  std::string line;
  
  // class helloworld extends java.lang.Object
  line=getline();
  if(!has_prefix(line, "class ")) throw parsing_errort("expected 'class'");

  while(!eof())
  {
    line=getline();
    
    #ifdef DEBUG
    std::cout << "rclass *** " << line << std::endl;
    #endif

    if(has_prefix(line, "SourceFile: "))
    {
    }
    else if(has_prefix(line, "minor version: "))
    {
    }
    else if(has_prefix(line, "major version: "))
    {
    }
    else if(line=="{")
    {
      rmembers();
    }
    else if(has_prefix(line, "const "))
    {
      rconstant(std::string(line, 6, std::string::npos));
    }
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
  
  // javap likes to get the _class_ name, not the file name,
  // so we strip the ".class" suffix.
  
  std::string stripped_file_name=
    has_suffix(file, ".class")?std::string(file, 0, file.size()-6):file;
  
  std::string command="javap";
  
  command+=" -c -l -private -verbose \""+stripped_file_name+"\"";
  command+=" 2>\""+stderr_file+"\" >\""+stdout_file+"\"";  

  // _popen isn't very reliable on WIN32
  // that's why we use system()
  int result=system(command.c_str());

  std::ifstream stdout_stream(stdout_file.c_str());

  if(!stdout_stream)
  {
    unlink(stdout_file.c_str());
    unlink(stderr_file.c_str());
    message_stream.error("javap failed (stdout_stream open failed)");
    return true;
  }

  javap_parsert javap_parser;
  javap_parser.in=&stdout_stream;  
  javap_parser.set_message_handler(message_handler);
  
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
