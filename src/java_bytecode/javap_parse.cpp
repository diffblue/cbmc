/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <sstream>
#include <cstdlib> // for system()
#include <map>

#include <util/parser.h>
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
#include "javap_parse.h"

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
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
    error() << p.msg << eom;
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
  source_location.set_file(std::string(line, s.size(), line.size()-s.size()-1));
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
  
  unsigned no=safe_string2unsigned(no_string);
  constantt &constant=constants[no];
  constant.kind=kind;
  constant.value_string=value;
  
  // the expressions are produced once all are read
}
  
/*******************************************************************\

Function: javap_parsert::post_process_constants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void javap_parsert::post_process_constants()
{
  for(constantst::iterator
      c_it=constants.begin();
      c_it!=constants.end();
      c_it++)
  {
    constantt &c=c_it->second;

    if(c.kind=="Method" || c.kind=="Field")
    {
      // this is #class.#NameAndType
      assert(!c.value_string.empty());
      std::size_t member_pos=c.value_string.find('#', 1);
      assert(member_pos!=std::string::npos);
      std::string class_string=constant(constant(c.value_string));
      std::string name_and_type=constant(std::string(c.value_string, member_pos, std::string::npos));
      assert(!name_and_type.empty()); // this is #name:#type
      std::size_t type_pos=name_and_type.find('#', 1);
      assert(type_pos!=std::string::npos);
      std::string type_string=constant(std::string(name_and_type, type_pos, std::string::npos));
      std::string member_string=constant(std::string(name_and_type, 0, type_pos-1));

      // for overloading
      std::string member_suffix=(c.kind=="Method")?":"+type_string:"";
      
      irep_idt identifier="java::"+slash_to_dot(class_string)+"."+member_string+member_suffix;
      typet type=java_type_from_string(type_string);
      
      c.value_expr=symbol_exprt(identifier, type);
      c.value_expr.set(ID_C_base_name, member_string);
    }
    else if(c.kind=="String")
    {
      // this is a ref to an Asciz,
      // in a stupid layering of custom UTF-8 and UTF-16
      c.value_expr=string_constantt(constant(c.value_string));
    }
    else if(c.kind=="class")
    {
      // this is just a ref to a string with the identifier
      irep_idt identifier="java::"+slash_to_dot(constant(c.value_string));
      c.value_expr=type_exprt(symbol_typet(identifier));
    }
    else if(c.kind=="Asciz" || c.kind=="NameAndType")
    {
      // nothing, only used indirectly
    }
    else if(c.kind=="int")
    {
      std::string number_str;

      for(size_t i=0; i<c.value_string.size(); i++)
      {
        if(!isdigit(c.value_string[i]) && c.value_string[i]!='-') break;
        number_str+=c.value_string[i];
      }

      mp_integer i=string2integer(number_str);
      c.value_expr=from_integer(i, java_int_type());
    }
    else if(c.kind=="long")
    {
      std::string number_str;

      for(size_t i=0; i<c.value_string.size(); i++)
      {
        if(!isdigit(c.value_string[i]) && c.value_string[i]!='-') break;
        number_str+=c.value_string[i];
      }

      mp_integer i=string2integer(number_str);
      c.value_expr=from_integer(i, java_long_type());
    }
    else if(c.kind=="float")
    {
      if(c.value_string=="Infinityf")
        c.value_expr=ieee_floatt::plus_infinity(ieee_float_spect::single_precision()).to_expr();
      else if(c.value_string=="-Infinityf")
        c.value_expr=ieee_floatt::plus_infinity(ieee_float_spect::single_precision()).to_expr();
      else if(c.value_string=="NaNf")
        c.value_expr=ieee_floatt::NaN(ieee_float_spect::single_precision()).to_expr();
      else
        c.value_expr=convert_float_literal(c.value_string);
    }
    else if(c.kind=="double")
    {
      if(c.value_string=="Infinityd")
        c.value_expr=ieee_floatt::plus_infinity(ieee_float_spect::single_precision()).to_expr();
      else if(c.value_string=="-Infinityd")
        c.value_expr=ieee_floatt::plus_infinity(ieee_float_spect::single_precision()).to_expr();
      else if(c.value_string=="NaNd")
        c.value_expr=ieee_floatt::NaN(ieee_float_spect::single_precision()).to_expr();
      else
        c.value_expr=convert_float_literal(c.value_string);
    }
    else
      throw std::string("unhandled constant: ")+id2string(c.kind);
  }
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
  instruction.address=unsafe_string2unsigned(id2string(t));
  
  t=token(); // :
  
  t=token(); // statement
  instruction.statement=t;

  while(lookahead()!="" && lookahead()!=";")
  {
    t=token(); // arguments
  
    if(t=="#")
    {
      // a constant from the constant table
      t=token();
      instruction.args.push_back(constants[unsafe_string2unsigned(id2string(t))].value_expr);
    }
    else if(t!="" && isdigit(t[0]))
      instruction.args.push_back(constant_exprt(t, integer_typet())); // some number
    else
      instruction.args.push_back(exprt(t)); // some string, e.g., primitive type

    if(lookahead()==",")
      token(); // eat ,
    else
      break;
  }
  
  // do we have a line number?
  if(address_to_line.find(instruction.address)!=address_to_line.end())
  {
    instruction.source_location.set_line(address_to_line[instruction.address]);
    instruction.source_location.set_file(source_location.get_file());
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
        unsafe_string2unsigned(std::string(line, 3+4+1, std::string::npos));
      unsigned address=
        unsafe_string2unsigned(std::string(line, line.find(':')+1, std::string::npos));
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
    else if(has_prefix(line, "  Signature: "))
    {
      m->signature=line.substr(13, std::string::npos);
    }
  }
}

/*******************************************************************\

Function: javap_parsert::rname

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt javap_parsert::rname()
{
  // read a sequence of '.' and identifiers
  std::string result;

  while(true)
  {
    irep_idt t=token();
    result+=id2string(t);
    if(lookahead()!=".") break;
    token(); // read .
    result+='.';
  }
  
  return result;
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
      identifier+='.';
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
  membert &m=dest_class.add_member();
  
  while(lookahead()==ID_public ||
        lookahead()==ID_private ||
        lookahead()==ID_protected ||
        lookahead()==ID_static ||
        lookahead()==ID_final ||
        lookahead()==ID_native)
  {
    irep_idt t=token(); // eat

    if(t==ID_static)
      m.is_static=true;
    else if(t==ID_native)
      m.is_native=true;
  }

  // constructor?
  if(lookahead()==dest_class.name)
  {
    // yes, constructor
    m.name=token();
    m.base_name=m.name;
  }
  else if(lookahead()=="{")
  {
    // static {};
    // These are static initializers, executed when the class is loaded.
    token();
    if(lookahead()=="}") token();
    m.name="{}";
    m.base_name=m.name;
  }
  else
  {
    // eat (return) type
    rtype();

    // get member name
    m.name=token();
    m.base_name=m.name;
  }
  
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
  
  c.name=rname();
  
  if(lookahead()=="extends")
  {
    token(); // read 'extends'
    c.extends=rname();
  }

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
      post_process_constants();
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

  javap_parsert javap_parser;
  javap_parser.in=&stdout_stream;  
  javap_parser.set_message_handler(message_handler);
  
  bool parser_result=javap_parser.parse();

  parse_tree.swap(javap_parser.parse_tree);

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
}
