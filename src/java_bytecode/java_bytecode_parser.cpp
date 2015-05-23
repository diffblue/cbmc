/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#if 0
#include <sstream>
#include <cstdlib> // for system()
#include <map>

#include <util/message_stream.h>
#include <util/tempfile.h>
#include <util/suffix.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/arith_tools.h>
#include <util/i2string.h>

#include <ansi-c/string_constant.h>
#include <ansi-c/literals/convert_float_literal.h>

#include "java_types.h"

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

//#define DEBUG
#endif

#include <util/parser.h>

#include "java_bytecode_parser.h"

#ifdef DEBUG
#include <iostream>
#endif

class java_bytecode_parsert:public parsert
{
public:
  virtual bool parse();
  
  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::membert membert;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  
  java_bytecode_parse_treet parse_tree;
 
protected: 
  #if 0
  void rgrammar();
  void rheader();
  void rclass();
  void rmembers(classt &dest_class);
  membert &rmember(classt &dest_class);
  void rconstant(const std::string &line);
  typet rtype();
  void rcode(membert &dest_member);
  irep_idt rname();

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
  
  // constant map, per-class
  class constantt
  {
  public:
    irep_idt kind;
    std::string value_string;
    exprt value_expr;
    
    constantt():value_expr(nil_exprt())
    {
    }
  };
  
  typedef std::map<unsigned, constantt> constantst;
  constantst constants;

  void post_process_constants();

  std::string constant(const std::string &ref)
  {
    // follow a #number
    assert(!ref.empty() && ref[0]=='#');
    return constants[unsafe_c_str2unsigned(ref.c_str()+1)].value_string;
  }
  
  typedef std::map<unsigned, unsigned> address_to_linet;
  address_to_linet address_to_line;
  
  // token scanner
  std::list<irep_idt> tokens;

  irep_idt token()
  {
    if(tokens.empty()) return irep_idt();
    irep_idt t=tokens.front();
    tokens.pop_front();
    return t;
  }
  
  inline irep_idt lookahead()
  {
    if(tokens.empty()) return irep_idt();
    return tokens.front();
  }
  
  void tokenize(const std::string &str);
  
  // java/lang/Object -> java.lang.Object
  static std::string slash_to_dot(const std::string &src)
  {
    std::string result=src;
    for(std::string::iterator it=result.begin(); it!=result.end(); it++)
      if(*it=='/') *it='.';
    return result;
  }
  #endif
};

/*******************************************************************\

Function: java_bytecode_parsert::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_parsert::parse()
{
  try
  {
  }
  
  catch(...)
  {
    error() << "parsing error" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: java_bytecode_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_parse(
  const std::string &file,
  java_bytecode_parse_treet &parse_tree,
  message_handlert &message_handler)
{
  #if 0
  message_streamt message_stream(message_handler);

  // use javap
  
  std::string stderr_file=get_temporary_file("tmp.stderr", "");
  std::string stdout_file=get_temporary_file("tmp.stdout", "");
  
  // javap likes to get the _class_ name, not the file name,
  // so we strip the ".class" suffix.
  
  std::string stripped_file_name=
    has_suffix(file, ".class")?std::string(file, 0, file.size()-6):file;
  
  std::string command="javap-1.6";
  
  command+=" -s -c -l -private -verbose \""+stripped_file_name+"\"";
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

  java_bytecode_parsert java_bytecode_parser;
  java_bytecode_parser.in=&stdout_stream;  
  java_bytecode_parser.set_message_handler(message_handler);
  
  bool parser_result=java_bytecode_parser.parse();

  parse_tree.swap(java_bytecode_parser.parse_tree);

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while(stderr_stream.read(&ch, 1))
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
  #endif
}
