/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/i2string.h>
#include <util/parser.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>

#include <ansi-c/string_constant.h>

#include "java_bytecode_parser.h"
#include "java_bytecode_parse_tree.h"
#include "java_types.h"
#include "bytecode_info.h"

#ifdef DEBUG
#include <iostream>
#endif

class java_bytecode_parsert:public parsert
{
public:
  java_bytecode_parsert()
  {
    get_bytecodes();
  }

  virtual bool parse();

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::classt::fieldst fieldst;
  typedef java_bytecode_parse_treet::classt::methodst methodst;
  typedef java_bytecode_parse_treet::methodt methodt;
  typedef java_bytecode_parse_treet::fieldt fieldt;
  typedef java_bytecode_parse_treet::methodt::instructionst instructionst;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  
  java_bytecode_parse_treet parse_tree;

  typedef unsigned char u1;
  typedef unsigned short u2;
  typedef unsigned int u4;
  typedef unsigned long long u8;
  
  struct pool_entryt
  {
    u1 tag;
    u2 ref1, ref2;
    irep_idt s;
    u8 number;
    exprt expr;
    pool_entryt():tag(0), ref1(0), ref2(0), number(0) { }
  };
  
  typedef std::vector<pool_entryt> constant_poolt;
  constant_poolt constant_pool;
 
protected: 
  class bytecodet
  {
  public:
    irep_idt mnemonic;
    char format;
  };
  
  std::vector<bytecodet> bytecodes;
  
  pool_entryt &pool_entry(u2 index)
  {
    if(index==0 || index>=constant_pool.size())
      throw "invalid constant pool index";
    return constant_pool[index];
  }
  
  exprt &constant(u2 index)
  {
    return pool_entry(index).expr;
  }
  
  void get_bytecodes()
  {
    // pre-hash the mnemonics, so we do this only once
    bytecodes.resize(256);
    for(const bytecode_infot *p=bytecode_info; p->mnemonic!=0; p++)
    {
      assert(p->opcode<bytecodes.size());
      bytecodes[p->opcode].mnemonic=p->mnemonic;
      bytecodes[p->opcode].format=p->format;
    }
  }  

  void rClassFile();
  void rconstant_pool();
  void rinterfaces(classt &parsed_class);
  void rfields(classt &parsed_class);
  void rmethods(classt &parsed_class);
  void rmethod(classt &parsed_class);
  void rclass_attribute(classt &parsed_class);
  void rmethod_attribute(methodt &method);
  void rcode_attribute(methodt &method);
  void rbytecode(methodt::instructionst &);
  void get_class_refs();
  
  void skip_bytes(unsigned bytes) const
  {
    for(unsigned i=0; i<bytes; i++)
    {
      if(!*in) throw "unexpected end of input file";
      in->get();
    }
  }
  
  u8 read_bytes(unsigned bytes) const
  {
    u8 result=0;
    for(unsigned i=0; i<bytes; i++)
    {
      if(!*in) throw "unexpected end of input file";
      result<<=8;
      result|=in->get();
    }
    return result;
  }

  u1 read_u1() const
  {
    return read_bytes(1);
  }
  
  inline u2 read_u2() const
  {
    return read_bytes(2);
  }
  
  u4 read_u4() const
  {
    return read_bytes(4);
  }
  
  u8 read_u8() const
  {
    return read_bytes(8);
  }

  // java/lang/Object -> java.lang.Object
  static std::string slash_to_dot(const std::string &src)
  {
    std::string result=src;
    for(std::string::iterator it=result.begin(); it!=result.end(); it++)
      if(*it=='/') *it='.';
    return result;
  }
};

#define CONSTANT_Class                7
#define CONSTANT_Fieldref             9
#define CONSTANT_Methodref           10
#define CONSTANT_InterfaceMethodref  11
#define CONSTANT_String               8
#define CONSTANT_Integer              3
#define CONSTANT_Float                4
#define CONSTANT_Long                 5
#define CONSTANT_Double               6
#define CONSTANT_NameAndType         12
#define CONSTANT_Utf8                 1
#define CONSTANT_MethodHandle        15
#define CONSTANT_MethodType          16
#define CONSTANT_InvokeDynamic       18

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
    rClassFile();
  }
  
  catch(const char *message)
  {
    error() << message << eom;
    return true;
  }
  
  catch(const std::string &message)
  {
    error() << message << eom;
    return true;
  }
  
  catch(...)
  {
    error() << "parsing error" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: java_bytecode_parsert::rClassFile

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define ACC_PUBLIC       0x0001
#define ACC_PRIVATE      0x0002
#define ACC_PROTECTED    0x0004
#define ACC_STATIC       0x0008
#define ACC_FINAL        0x0010
#define ACC_SYNCHRONIZED 0x0020
#define ACC_BRIDGE       0x0040
#define ACC_VARARGS      0x0080
#define ACC_NATIVE       0x0100
#define ACC_ABSTRACT     0x0400
#define ACC_STRICT       0x0800
#define ACC_SYNTHETIC    0x1000

void java_bytecode_parsert::rClassFile()
{
  parse_tree.loading_successful=false;

  u4 magic=read_u4();
  u2 minor_version=read_u2(), major_version=read_u2();
  
  if(magic!=0xCAFEBABE) throw "wrong magic";

  if(major_version<44)
    throw "unexpected major version";
  
  rconstant_pool();

  classt &parsed_class=parse_tree.parsed_class;

  u2 access_flags=read_u2();
  u2 this_class=read_u2();
  u2 super_class=read_u2();

  parsed_class.name=
    constant(this_class).type().get(ID_C_base_name);

  parsed_class.extends=
    constant(super_class).type().get(ID_C_base_name);

  rinterfaces(parsed_class);
  
  rfields(parsed_class);
  rmethods(parsed_class);
  
  u2 attributes_count=read_u2();

  for(unsigned j=0; j<attributes_count; j++)
    rclass_attribute(parsed_class);

  get_class_refs();

  parse_tree.loading_successful=true;
}
  
/*******************************************************************\

Function: java_bytecode_parsert::get_class_refs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::get_class_refs()
{
  // Get the class references for the benefit of a dependency
  // analysis.

  for(constant_poolt::iterator
      it=constant_pool.begin();
      it!=constant_pool.end();
      it++)
  {
    if(it->tag==CONSTANT_Class)
    {
      if(it->expr.type().id()==ID_symbol)
        parse_tree.class_refs.insert(it->expr.type().get(ID_C_base_name));
      else if(it->expr.type().id()==ID_array)
        parse_tree.class_refs.insert(it->expr.type().subtype().get(ID_C_base_name));
    }
  }
  
  std::set<irep_idt> signatures;

  for(methodst::const_iterator m_it=parse_tree.parsed_class.methods.begin();
      m_it!=parse_tree.parsed_class.methods.end();
      m_it++)
    signatures.insert(m_it->signature);

  for(fieldst::const_iterator m_it=parse_tree.parsed_class.fields.begin();
      m_it!=parse_tree.parsed_class.fields.end();
      m_it++)
    signatures.insert(m_it->signature);

  for(std::set<irep_idt>::const_iterator
      it=signatures.begin();
      it!=signatures.end();
      it++)
  {
    // we scan for L<name>;
    const std::string &s=id2string(*it);
    for(std::string::const_iterator s_it=s.begin();
        s_it!=s.end(); s_it++)
    {
      if(*s_it=='L')
      {
        s_it++;
        std::string dest;
        while(s_it!=s.end() && *s_it!=';')
        {
          dest+=*s_it;
          s_it++;
        }
        
        parse_tree.class_refs.insert(slash_to_dot(dest));
      }
    }
  }
}

/*******************************************************************\

Function: java_bytecode_parsert::rconstant_pool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::rconstant_pool()
{
  u2 constant_pool_count=read_u2();
  if(constant_pool_count==0) throw "invalid constant_pool_count";
  
  constant_pool.resize(constant_pool_count);
  
  for(constant_poolt::iterator
      it=constant_pool.begin();
      it!=constant_pool.end();
      it++)
  {
    // the first entry isn't used
    if(it==constant_pool.begin()) continue;
    
    it->tag=read_u1();
    
    switch(it->tag)
    {
    case CONSTANT_Class:
      it->ref1=read_u2();
      break;

    case CONSTANT_Fieldref:
    case CONSTANT_Methodref:
    case CONSTANT_InterfaceMethodref:
    case CONSTANT_NameAndType:
    case CONSTANT_InvokeDynamic:
      it->ref1=read_u2();
      it->ref2=read_u2();
      break;
      
    case CONSTANT_String:
    case CONSTANT_MethodType:
      it->ref1=read_u2();
      break;

    case CONSTANT_Integer:
    case CONSTANT_Float:
      it->number=read_u4();
      break;

    case CONSTANT_Long:
    case CONSTANT_Double:
      it->number=read_u8();
      // Eight-byte constants take up two entires
      // in the constant_pool table, for annoying this programmer.
      if(it==constant_pool.end()) throw "invalid double entry";
      it++;
      it->tag=0;
      break;

    case CONSTANT_Utf8:
      {
        u2 bytes=read_u2();
        std::string s;
        s.resize(bytes);
        for(std::string::iterator s_it=s.begin(); s_it!=s.end(); s_it++)
          *s_it=read_u1();
        it->s=s; // hashes
      }
      break;

    case CONSTANT_MethodHandle:
      it->ref1=read_u1();
      it->ref2=read_u2();
      break;

    default:
      throw std::string("unknown constant pool entry (")+
            i2string(it->tag)+")";
    }
  }

  // we do a bit of post-processing after we have them all
  for(constant_poolt::iterator
      it=constant_pool.begin();
      it!=constant_pool.end();
      it++)
  {
    // the first entry isn't used
    if(it==constant_pool.begin()) continue;
    
    switch(it->tag)
    {
    case CONSTANT_Class:
      {
        const std::string &s=id2string(pool_entry(it->ref1).s);
      
        if(!s.empty() &&
           s[0]=='[')
        {
          it->expr=type_exprt(java_type_from_string(s));
        }
        else
        {
          std::string class_name=slash_to_dot(s);
          irep_idt identifier="java::"+class_name;
          symbol_typet symbol_type(identifier);
          symbol_type.set(ID_C_base_name, class_name);
          it->expr=type_exprt(symbol_type);
        }
      }
      break;

    case CONSTANT_Fieldref:
      {
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        const pool_entryt &name_entry=pool_entry(nameandtype_entry.ref1);
        const pool_entryt &type_entry=pool_entry(nameandtype_entry.ref2);
        const pool_entryt &class_entry=pool_entry(it->ref1);
        const pool_entryt &class_name_entry=pool_entry(class_entry.ref1);
        typet type=java_type_from_string(id2string(type_entry.s));
        
        irep_idt class_identifier=
          "java::"+slash_to_dot(id2string(class_name_entry.s));

        exprt fieldref("fieldref", type);
        fieldref.set(ID_class, class_identifier);
        fieldref.set(ID_component_name, name_entry.s);

        it->expr=fieldref;
      }
      break;
      
    case CONSTANT_Methodref:
    case CONSTANT_InterfaceMethodref:
      {
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        const pool_entryt &name_entry=pool_entry(nameandtype_entry.ref1);
        const pool_entryt &type_entry=pool_entry(nameandtype_entry.ref2);
        const pool_entryt &class_entry=pool_entry(it->ref1);
        const pool_entryt &class_name_entry=pool_entry(class_entry.ref1);
        typet type=java_type_from_string(id2string(type_entry.s));
        
        irep_idt identifier=
          "java::"+slash_to_dot(id2string(class_name_entry.s))+
          "."+id2string(name_entry.s)+
          ":"+id2string(type_entry.s);

        symbol_exprt symbol_expr(identifier, type);
        symbol_expr.set(ID_C_base_name, name_entry.s);

        it->expr=symbol_expr;
      }
      break;

    case CONSTANT_String:
      it->expr=string_constantt(pool_entry(it->ref1).s);
      break;

    case CONSTANT_Integer:
      it->expr=from_integer(it->number, java_int_type());
      break;

    case CONSTANT_Float:
      {
        ieee_floatt value(ieee_float_spect::single_precision());
        value.unpack(it->number);
        it->expr=value.to_expr();
      }
      break;
      
    case CONSTANT_Long:
      it->expr=from_integer(it->number, java_long_type());
      break;

    case CONSTANT_Double:
      {
        ieee_floatt value(ieee_float_spect::double_precision());
        value.unpack(it->number);
        it->expr=value.to_expr();
      }
      break;

    case CONSTANT_NameAndType:
      {
        it->expr.id("nameandtype");
      }
      break;

    case CONSTANT_MethodHandle:
      {
        it->expr.id("methodhandle");
      }
      break;

    case CONSTANT_MethodType:
      {
        it->expr.id("methodtype");
      }
      break;

    case CONSTANT_InvokeDynamic:
      {
        it->expr.id("invokedynamic");
      }
      break;

    default:;
    }
  }
}

/*******************************************************************\

Function: java_bytecode_parsert::rinterfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::rinterfaces(classt &parsed_class)
{
  u2 interfaces_count=read_u2();

  for(unsigned i=0; i<interfaces_count; i++)
    parsed_class.implements.push_back(pool_entry(read_u2()).s);
}

/*******************************************************************\

Function: java_bytecode_parsert::rfields

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::rfields(classt &parsed_class)
{
  u2 fields_count=read_u2();

  for(unsigned i=0; i<fields_count; i++)
  {
    fieldt &field=parsed_class.add_field();
    
    u2 access_flags=read_u2();
    u2 name_index=read_u2();
    u2 descriptor_index=read_u2();
    u2 attributes_count=read_u2();
    
    field.name=pool_entry(name_index).s;
    field.is_static=access_flags&ACC_STATIC;
    field.is_final=access_flags&ACC_FINAL;
    field.signature=id2string(pool_entry(descriptor_index).s);

    for(unsigned j=0; j<attributes_count; j++)
    {
      u2 attribute_name_index=read_u2();
      u4 attribute_length=read_u4();
      skip_bytes(attribute_length);
    }
  }
}

/*******************************************************************\

Function: java_bytecode_parsert::rbytecode

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define T_BOOLEAN 4
#define T_CHAR    5
#define T_FLOAT   6
#define T_DOUBLE  7
#define T_BYTE    8
#define T_SHORT   9
#define T_INT    10
#define T_LONG   11

void java_bytecode_parsert::rbytecode(
  methodt::instructionst &instructions)
{
  u4 code_length=read_u4();
  
  unsigned address;

  for(address=0; address<code_length; address++)
  {
    bool wide_instruction=false;
    unsigned start_of_instruction=address;
    
    u1 bytecode=read_u1();
    
    if(bytecode==0xc4) // wide
    {
      wide_instruction=true;
      address++;
      bytecode=read_u1();
    }
    
    instructions.push_back(instructiont());
    instructiont &instruction=instructions.back();
    instruction.statement=bytecodes[bytecode].mnemonic;
    instruction.address=start_of_instruction;
    
    switch(bytecodes[bytecode].format)
    {
    case ' ': // no further bytes
      break;

    case 'c': // a constant_pool index (one byte)
      if(wide_instruction)
      {
        instruction.args.push_back(constant(read_u2()));
        address+=2;
      }
      else
      {
        instruction.args.push_back(constant(read_u1()));
        address+=1;
      }
      break;

    case 'C': // a constant_pool index (two bytes)
      instruction.args.push_back(constant(read_u2()));
      address+=2;
      break;
      
    case 'b': // a signed byte
      {
        signed char c=read_u1();
        instruction.args.push_back(from_integer(c, integer_typet()));
      }
      address+=1;
      
      break;

    case 'o': // two byte branch offset
      {
        signed short offset=read_u2();
        instruction.args.push_back(from_integer(address+offset, integer_typet()));
      }
      address+=2;
      break;

    case 'O': // four byte branch offset
      {
        signed int offset=read_u4();
        instruction.args.push_back(from_integer(address+offset, integer_typet()));
      }
      address+=4;
      break;

    case 'v': // local variable index (one byte)
      {
        u1 v=read_u1();
        instruction.args.push_back(from_integer(v, integer_typet()));
      }
      address+=1;
      break;
      
    case 'V': // local variable index (one byte) plus one signed byte
      if(wide_instruction)
      {
        u2 v=read_u2();
        instruction.args.push_back(from_integer(v, integer_typet()));
        signed short c=read_u2();
        instruction.args.push_back(from_integer(c, integer_typet()));
      }
      else
      {
        u1 v=read_u1();
        instruction.args.push_back(from_integer(v, integer_typet()));
        signed char c=read_u1();
        instruction.args.push_back(from_integer(c, integer_typet()));
      }
      address+=2;
      break;
      
    case 'I': // two byte constant_pool index plus two bytes
      {
        u2 c=read_u2();
        instruction.args.push_back(constant(c));
        u1 b1=read_u1();
        instruction.args.push_back(from_integer(b1, integer_typet()));
        u1 b2=read_u1();
        instruction.args.push_back(from_integer(b2, integer_typet()));
      }
      address+=4;
      break;
      
    case 'L': // lookupswitch
      {
        // first a pad to 32-bit align
        while((address&3)!=0) { read_u1(); address++; }
        
        // now default value
        u4 default_value=read_u4();
        address+=4;
        
        // number of pairs
        u4 npairs=read_u4();
        address+=4;
        
        for(unsigned i=0; i<npairs; i++)
        {
          u4 match=read_u4();
          u4 offset=read_u4();
          address+=8;
        }
      }
      break;
      
    case 'T': // tableswitch
      {
        // first a pad to 32-bit align
        while((address&3)!=0) { read_u1(); address++; }
        
        // now default value
        u4 default_value=read_u4();
        address+=4;

        // now low value
        u4 low_value=read_u4();
        address+=4;
        
        // now high value
        u4 high_value=read_u4();
        address+=4;

        // there are high-low+1 offsets
        for(unsigned i=low_value; i<=high_value; i++)
        {
          u4 offset=read_u4();
          address+=4;
        }
      }
      break;
      
    case 'm': // multianewarray: constant-pool index plus one unsigned byte
      {
        u2 c=read_u2(); // constant-pool index
        instruction.args.push_back(constant(c));
        u1 dimensions=read_u1(); // number of dimensions
        instruction.args.push_back(from_integer(dimensions, integer_typet()));
        address+=3;
      }
      break;
      
    case 't': // array subtype, one byte
      {
        typet t;
        switch(read_u1())
        {
        case T_BOOLEAN: t.id(ID_bool); break;
        case T_CHAR: t.id(ID_char); break;
        case T_FLOAT: t.id(ID_float); break;
        case T_DOUBLE: t.id(ID_double); break;
        case T_BYTE: t.id(ID_byte); break;
        case T_SHORT: t.id(ID_short); break;
        case T_INT: t.id(ID_int); break;
        case T_LONG: t.id(ID_long); break;
        default:;
        }
        instruction.args.push_back(type_exprt(t));
      }
      address+=1;
      break;
      
    case 's': // a signed short
      {
        signed short s=read_u2();
        instruction.args.push_back(from_integer(s, integer_typet()));
      }
      address+=2;
      break;

    default:;
    }
  }
  
  if(address!=code_length)
    throw "bytecode length mismatch";
}

/*******************************************************************\

Function: java_bytecode_parsert::rmethod_attribute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::rmethod_attribute(methodt &method)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();
  
  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="Code")
  {
    u2 max_stack=read_u2();
    u2 max_locals=read_u2();

    rbytecode(method.instructions);

    u2 exception_table_length=read_u2();

    for(unsigned e=0; e<exception_table_length; e++)
    {
      u2 start_pc=read_u2();
      u2 end_pc=read_u2();
      u2 handler_pc=read_u2();
      u2 catch_type=read_u2();
    }

    u2 attributes_count=read_u2();

    for(unsigned j=0; j<attributes_count; j++)
      rcode_attribute(method);
      
    irep_idt line_number;
      
    // add missing line numbers
    for(methodt::instructionst::iterator
        it=method.instructions.begin(); 
        it!=method.instructions.end();
        it++)
    {
      if(!it->source_location.get_line().empty())
        line_number=it->source_location.get_line();
      else if(!line_number.empty())
        it->source_location.set_line(line_number);
    }
    
  }
  else
    skip_bytes(attribute_length);
}

/*******************************************************************\

Function: java_bytecode_parsert::rcode_attribute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::rcode_attribute(methodt &method)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();
  
  irep_idt attribute_name=pool_entry(attribute_name_index).s;
  
  if(attribute_name=="LineNumberTable")
  {
    // address -> instructiont
    typedef std::map<unsigned, methodt::instructionst::iterator> instruction_mapt;
    instruction_mapt instruction_map;

    for(methodt::instructionst::iterator
        it=method.instructions.begin(); 
        it!=method.instructions.end();
        it++)
    {
      instruction_map[it->address]=it;
    }
  
    u2 line_number_table_length=read_u2();

    for(unsigned i=0; i<line_number_table_length; i++)
    {
      u2 start_pc=read_u2();
      u2 line_number=read_u2();

      // annotate the bytecode program      
      instruction_mapt::const_iterator it=
        instruction_map.find(start_pc);
      
      if(it!=instruction_map.end())
        it->second->source_location.set_line(line_number);
    }
  }
  else
    skip_bytes(attribute_length);
}

/*******************************************************************\

Function: java_bytecode_parsert::rclass_attribute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::rclass_attribute(classt &parsed_class)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;
  
  if(attribute_name=="SourceFile")
  {
    u2 sourcefile_index=read_u2();
    irep_idt sourcefile_name=pool_entry(sourcefile_index).s;
    
    for(methodst::iterator m_it=parsed_class.methods.begin();
        m_it!=parsed_class.methods.end();
        m_it++)
    {
      for(instructionst::iterator i_it=m_it->instructions.begin();
          i_it!=m_it->instructions.end();
          i_it++)
      {
        if(!i_it->source_location.get_line().empty())
          i_it->source_location.set_file(sourcefile_name);
      }
    }
  }
  else
    skip_bytes(attribute_length);
}

/*******************************************************************\

Function: java_bytecode_parsert::rmethods

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parsert::rmethods(classt &parsed_class)
{
  u2 methods_count=read_u2();

  for(unsigned j=0; j<methods_count; j++)
    rmethod(parsed_class);
}

/*******************************************************************\

Function: java_bytecode_parsert::rmethod

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define ACC_PUBLIC     0x0001
#define ACC_PRIVATE    0x0002
#define ACC_PROTECTED  0x0004
#define ACC_STATIC     0x0008
#define ACC_FINAL      0x0010
#define ACC_SUPER      0x0020
#define ACC_VOLATILE   0x0040
#define ACC_TRANSIENT  0x0080
#define ACC_INTERFACE  0x0200
#define ACC_ABSTRACT   0x0400
#define ACC_SYNTHETIC  0x1000
#define ACC_ANNOTATION 0x2000
#define ACC_ENUM       0x4000

void java_bytecode_parsert::rmethod(classt &parsed_class)
{
  methodt &method=parsed_class.add_method();

  u2 access_flags=read_u2();
  u2 name_index=read_u2();
  u2 descriptor_index=read_u2();

  method.is_final=access_flags&ACC_FINAL;  
  method.is_static=access_flags&ACC_STATIC;
  method.is_abstract=access_flags&ACC_ABSTRACT;
  method.is_public=access_flags&ACC_PUBLIC;
  method.is_protected=access_flags&ACC_PROTECTED;
  method.is_private=access_flags&ACC_PRIVATE;
  method.is_synchronized=access_flags&ACC_SYNCHRONIZED;
  method.is_native=access_flags&ACC_NATIVE;
  method.name=pool_entry(name_index).s;
  method.base_name=pool_entry(name_index).s;
  method.signature=id2string(pool_entry(descriptor_index).s);

  u2 attributes_count=read_u2();

  for(unsigned j=0; j<attributes_count; j++)
    rmethod_attribute(method);
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
  std::ifstream in(file.c_str(), std::ios::binary);

  if(!in)
  {
    messaget message(message_handler);
    message.error() << "failed to open input file `"
                    << file << '\'' << messaget::eom;
    return true;
  }

  java_bytecode_parsert java_bytecode_parser;
  java_bytecode_parser.in=&in;
  java_bytecode_parser.set_message_handler(message_handler);
  
  bool parser_result=java_bytecode_parser.parse();

  parse_tree.swap(java_bytecode_parser.parse_tree);

  return parser_result;
}
