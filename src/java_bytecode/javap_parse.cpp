/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>
#include <sstream>

#include <util/parser.h>
#include <util/message_stream.h>
#include <util/tempfile.h>
#include <util/suffix.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/ieee_float.h>

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

//#define DEBUG

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
  
  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::membert membert;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  
  java_bytecode_parse_treet parse_tree;
 
protected: 
  void rgrammar();
  void rcompiled_from();
  void rclass();
  void rmembers(classt &dest_class);
  membert &rmember(classt &dest_class);
  void rconstant(const std::string &line);
  typet rtype();
  void rcode(membert &dest_member);

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
  
  // constant map
  class constantt
  {
  public:
    irep_idt kind, value;
  };
  
  typedef std::map<unsigned, constantt> constantst;
  constantst constants;
  
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

Function: javap_parsert::tokenize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::tokenize(const std::string &str)
{
  // split up into tokens
  std::string t;
  tokens.clear();

  for(std::size_t s=0; s<str.size(); s++)
  {
    char ch=str[s];

    if(isalnum(ch) || ch=='.' || ch=='_' || ch=='$')
      t+=ch;
    else
    {
      if(t!="") { tokens.push_back(t); t.clear(); }
      
      if(ch==' ' || ch=='\t' || ch=='\r' || ch=='\n')
      {
        // ignore whitespace
      }
      else
      {
        // single-character token
        t+=ch;
        tokens.push_back(t);
        t.clear();
      }
    }
  }
  
  if(t!="")
    tokens.push_back(t);
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
  // const #1 = Method	#6.#15;
  std::size_t no_pos=line.find('#');
  std::size_t eq_pos=line.find("= ");
  std::size_t tab_pos=line.find('\t');
  
  std::string no_string=std::string(line, no_pos+1, eq_pos-no_pos-2);
  std::string kind=std::string(line, eq_pos+2, tab_pos-eq_pos-2);
  std::string value=std::string(line, tab_pos+1, std::string::npos);  
  
  // strip trailing ;
  if(has_suffix(value, ";"))
    value.resize(value.size()-1);
  
  if(kind=="Method" ||
     kind=="class")
  {
    std::size_t pos=value.find("//  ");
    if(pos!=std::string::npos)
      value=std::string(value, pos+4, std::string::npos);
  }
  
  unsigned no=atoi(no_string.c_str());
  constants[no].kind=kind;
  constants[no].value=value;
}
  
/*******************************************************************\

Function: javap_parsert::rcode

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rcode(membert &dest_member)
{
  instructiont &instruction=dest_member.add_instruction();

  //    0:	bipush	123
  irep_idt t;
  t=token(); // address
  instruction.address=atoi(t.c_str());
  
  t=token(); // :
  
  t=token(); // statement
  instruction.statement=t;

  t=token(); // argument
  
  if(t=="#")
  {
    t=token();
    instruction.argument=constants[atoi(t.c_str())].value;
  }
  else
    instruction.argument=t;
  
  // do we have a line number?
  if(address_to_line.find(instruction.address)!=address_to_line.end())
  {
    instruction.location.set_line(address_to_line[instruction.address]);
    instruction.location.set_file(filename);
  }
}

/*******************************************************************\

Function: javap_parsert::rmembers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::rmembers(classt &dest_class)
{
  std::string line;
  membert *m=NULL;
  
  while(!eof())
  {
    line=getline();
    
    #ifdef DEBUG
    std::cout << "rmembers *** " << line << std::endl;
    #endif

    if(line=="}") // end of members
      return;
    else if(line!="" && line[0]!=' ')
    {
      tokenize(line);
      m=&rmember(dest_class);
    }
    else if(has_prefix(line, "   line "))
    {
      unsigned line_no=
        atoi(std::string(line, 3+4+1, std::string::npos).c_str());
      unsigned address=
        atoi(std::string(line, line.find(':')+1, std::string::npos).c_str());
      address_to_line[address]=line_no;
    }
    else if(line.size()>=4 &&
            line[0]==' ' && line[1]==' ' && line[2]==' ' &&
            isdigit(line[3]))
    {
      // code
      tokenize(line);
      rcode(*m);
    }
  }
}

/*******************************************************************\

Function: javap_parsert::rtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet javap_parsert::rtype()
{
  typet type;
  irep_idt t=token();

  #if 0
  if(t==ID_void)
    type=empty_typet();
  else if(t==ID_int)
    type=signedbv_typet(32); // 32-bit signed two's complement integer.
  else if(t==ID_byte)
    type=signedbv_typet(8);  // 8-bit signed two's complement integer.
  else if(t==ID_short)
    type=signedbv_typet(16); // 16-bit signed two's complement integer.
  else if(t==ID_long)
    type=signedbv_typet(64); // 64-bit signed two's complement integer.
  else if(t==ID_float)
    type=ieee_float_spect::single_precision().to_type();  // 32-bit float
  else if(t==ID_double)
    type=ieee_float_spect::double_precision().to_type();  // 64-bit float
  else if(t==ID_boolean)
    type=bool_typet();
  else if(t==ID_char)
    type=unsignedbv_typet(16); // 16-bit Unicode character
  else
  {
    // must be identifier
  }
  #endif

  if(t==ID_void || t==ID_int || t==ID_byte || t==ID_short ||
     t==ID_long || t==ID_float || t==ID_double || t==ID_boolean ||
     t==ID_char)
    type.id(t);
  else
  {
    // identifier
    type.id(ID_symbol);
    std::string identifier=id2string(t);
    while(lookahead()==".")
    {
      token(); // read .
      identifier+=".";
      identifier+=id2string(token());
    }
    type.set(ID_identifier, identifier);
  }
  
  // postfix
  
  if(lookahead()=="[")
  {
    token(); // read [
    if(lookahead()=="]")
    {
      token(); // read ]
      array_typet tmp;
      tmp.subtype()=type;
      type=tmp;
    }
  }
  
  return type;
}

/*******************************************************************\

Function: javap_parsert::rmember

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

javap_parsert::membert &javap_parsert::rmember(classt &dest_class)
{
  while(lookahead()==ID_public ||
        lookahead()==ID_private ||
        lookahead()==ID_protected ||
        lookahead()==ID_static)
  {
    token();
  }

  membert &m=dest_class.add_member();
  
  // constructor?
  if(lookahead()==dest_class.name)
  {
    // yes, constructor
  }
  else
  {
    // get type
    m.type=rtype();
  }

  // get member name
  m.name=token();

  // get postfix
  if(lookahead()=="(")
  {
    token(); // get (
    m.method=true;
    
    // parameter list
    while(lookahead()!=irep_idt())
    {
      if(lookahead()==")")
      {
        token(); // get )
        break;
      }
      else
      {
        typet p_type=rtype();
        m.parameters.push_back(code_typet::parametert());
        m.parameters.back().type()=p_type;
        if(lookahead()==",") token();
      }
    }
  }

  // read ;
  token();
  
  return m;
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
  tokenize(line);

  if(token()!=ID_class)
    throw parsing_errort("expected 'class'");

  classt &c=parse_tree.add_class();
  
  c.name=token();
  
  if(token()!="extends")
    throw parsing_errort("expected 'extends'");

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
      rmembers(c);
    }
    else if(has_prefix(line, "const "))
    {
      rconstant(line);
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

  parse_tree.swap(javap_parser.parse_tree);

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
