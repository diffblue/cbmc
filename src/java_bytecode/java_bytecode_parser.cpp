/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_parser.h"

#include <algorithm>
#include <fstream>
#include <map>
#include <string>

#include <util/parser.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/prefix.h>

#include <ansi-c/string_constant.h>

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
  typedef java_bytecode_parse_treet::annotationt annotationt;
  typedef java_bytecode_parse_treet::annotationst annotationst;

  java_bytecode_parse_treet parse_tree;

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
    {
      error() << "invalid constant pool index (" << index << ")" << eom;
      throw 0;
    }

    return constant_pool[index];
  }

  exprt &constant(u2 index)
  {
    return pool_entry(index).expr;
  }

  const typet type_entry(u2 index)
  {
    return java_type_from_string(id2string(pool_entry(index).s));
  }

  void get_bytecodes()
  {
    // pre-hash the mnemonics, so we do this only once
    bytecodes.resize(256);
    for(const bytecode_infot *p=bytecode_info; p->mnemonic!=nullptr; p++)
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
  void rRuntimeAnnotation_attribute(annotationst &);
  void rRuntimeAnnotation(annotationt &);
  void relement_value_pairs(annotationt::element_value_pairst &);
  void relement_value_pair(annotationt::element_value_pairt &);
  void rmethod_attribute(methodt &method);
  void rfield_attribute(fieldt &);
  void rcode_attribute(methodt &method);
  void read_verification_type_info(methodt::verification_type_infot &);
  void rbytecode(methodt::instructionst &);
  void get_class_refs();
  void get_class_refs_rec(const typet &);
  void parse_local_variable_type_table(methodt &method);

  void skip_bytes(std::size_t bytes)
  {
    for(std::size_t i=0; i<bytes; i++)
    {
      if(!*in)
      {
        error() << "unexpected end of bytecode file" << eom;
        throw 0;
      }
      in->get();
    }
  }

  u8 read_bytes(size_t bytes)
  {
    u8 result=0;
    for(size_t i=0; i<bytes; i++)
    {
      if(!*in)
      {
        error() << "unexpected end of bytecode file" << eom;
        throw 0;
      }
      result<<=8;
      result|=in->get();
    }
    return result;
  }

  u1 read_u1()
  {
    return (u1)read_bytes(1);
  }

  inline u2 read_u2()
  {
    return (u2)read_bytes(2);
  }

  u4 read_u4()
  {
    return (u4)read_bytes(4);
  }

  u8 read_u8()
  {
    return read_bytes(8);
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

#define VTYPE_INFO_TOP         0
#define VTYPE_INFO_INTEGER     1
#define VTYPE_INFO_FLOAT       2
#define VTYPE_INFO_LONG        3
#define VTYPE_INFO_DOUBLE      4
#define VTYPE_INFO_ITEM_NULL   5
#define VTYPE_INFO_UNINIT_THIS 6
#define VTYPE_INFO_OBJECT      7
#define VTYPE_INFO_UNINIT      8

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
#define ACC_ENUM         0x4000

#ifdef _MSC_VER
#define UNUSED
#else
#define UNUSED __attribute__((unused))
#endif

void java_bytecode_parsert::rClassFile()
{
  parse_tree.loading_successful=false;

  u4 magic=read_u4();
  u2 UNUSED minor_version=read_u2();
  u2 major_version=read_u2();

  if(magic!=0xCAFEBABE)
  {
    error() << "wrong magic" << eom;
    throw 0;
  }

  if(major_version<44)
  {
    error() << "unexpected major version" << eom;
    throw 0;
  }

  rconstant_pool();

  classt &parsed_class=parse_tree.parsed_class;

  u2 access_flags=read_u2();
  u2 this_class=read_u2();
  u2 super_class=read_u2();

  parsed_class.is_abstract=(access_flags&ACC_ABSTRACT)!=0;
  parsed_class.is_enum=(access_flags&ACC_ENUM)!=0;
  parsed_class.is_public=(access_flags&ACC_PUBLIC)!=0;
  parsed_class.is_protected=(access_flags&ACC_PROTECTED)!=0;
  parsed_class.is_private=(access_flags&ACC_PRIVATE)!=0;
  parsed_class.name=
    constant(this_class).type().get(ID_C_base_name);

  if(super_class!=0)
    parsed_class.extends=
      constant(super_class).type().get(ID_C_base_name);

  rinterfaces(parsed_class);
  rfields(parsed_class);
  rmethods(parsed_class);

  // count elements of enum
  if(parsed_class.is_enum)
    for(fieldt &field : parse_tree.parsed_class.fields)
      if(field.is_enum)
        parse_tree.parsed_class.enum_elements++;

  u2 attributes_count=read_u2();

  for(std::size_t j=0; j<attributes_count; j++)
    rclass_attribute(parsed_class);

  get_class_refs();

  parse_tree.loading_successful=true;
}

void java_bytecode_parsert::get_class_refs()
{
  // Get the class references for the benefit of a dependency
  // analysis.

  for(const auto &c : constant_pool)
  {
    switch(c.tag)
    {
    case CONSTANT_Class:
      get_class_refs_rec(c.expr.type());
      break;

    case CONSTANT_NameAndType:
      {
        typet t=java_type_from_string(id2string(pool_entry(c.ref2).s));
        get_class_refs_rec(t);
      }
      break;

    default: {}
    }
  }

  for(const auto &field : parse_tree.parsed_class.fields)
  {
    typet field_type;
    if(field.signature.has_value())
    {
      field_type=java_type_from_string(
        field.signature.value(),
        "java::"+id2string(parse_tree.parsed_class.name));
    }
    else
      field_type=java_type_from_string(field.descriptor);

    get_class_refs_rec(field_type);
  }

  for(const auto &method : parse_tree.parsed_class.methods)
  {
    typet method_type;
    if(method.signature.has_value())
    {
      method_type=java_type_from_string(
        method.signature.value(),
        "java::"+id2string(parse_tree.parsed_class.name));
    }
    else
      method_type=java_type_from_string(method.descriptor);

    get_class_refs_rec(method_type);
    for(const auto &var : method.local_variable_table)
    {
      typet var_type;
      if(var.signature.has_value())
      {
        var_type=java_type_from_string(
          var.signature.value(),
          "java::"+id2string(parse_tree.parsed_class.name));
      }
      else
        var_type=java_type_from_string(var.descriptor);
      get_class_refs_rec(var_type);
    }
  }
}

void java_bytecode_parsert::get_class_refs_rec(const typet &src)
{
  if(src.id()==ID_code)
  {
    const code_typet &ct=to_code_type(src);
    const typet &rt=ct.return_type();
    get_class_refs_rec(rt);
    for(const auto &p : ct.parameters())
      get_class_refs_rec(p.type());
  }
  else if(src.id()==ID_symbol)
  {
    irep_idt name=src.get(ID_C_base_name);
    if(has_prefix(id2string(name), "array["))
    {
      const typet &element_type=
        static_cast<const typet &>(src.find(ID_C_element_type));
      get_class_refs_rec(element_type);
    }
    else
      parse_tree.class_refs.insert(name);
  }
  else if(src.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(src);
    for(const auto &c : struct_type.components())
      get_class_refs_rec(c.type());
  }
  else if(src.id()==ID_pointer)
    get_class_refs_rec(src.subtype());
}

void java_bytecode_parsert::rconstant_pool()
{
  u2 constant_pool_count=read_u2();
  if(constant_pool_count==0)
  {
    error() << "invalid constant_pool_count" << eom;
    throw 0;
  }

  constant_pool.resize(constant_pool_count);

  for(constant_poolt::iterator
      it=constant_pool.begin();
      it!=constant_pool.end();
      it++)
  {
    // the first entry isn't used
    if(it==constant_pool.begin())
      continue;

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
      // Eight-byte constants take up two entries
      // in the constant_pool table, for annoying this programmer.
      if(it==constant_pool.end())
      {
        error() << "invalid double entry" << eom;
        throw 0;
      }
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
      error() << "unknown constant pool entry (" << it->tag << ")"
              << eom;
      throw 0;
    }
  }

  // we do a bit of post-processing after we have them all
  for(constant_poolt::iterator
      it=constant_pool.begin();
      it!=constant_pool.end();
      it++)
  {
    // the first entry isn't used
    if(it==constant_pool.begin())
      continue;

    switch(it->tag)
    {
    case CONSTANT_Class:
      {
        const std::string &s=id2string(pool_entry(it->ref1).s);
        it->expr=type_exprt(java_classname(s));
      }
      break;

    case CONSTANT_Fieldref:
      {
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        const pool_entryt &name_entry=pool_entry(nameandtype_entry.ref1);
        const pool_entryt &class_entry=pool_entry(it->ref1);
        const pool_entryt &class_name_entry=pool_entry(class_entry.ref1);
        typet type=type_entry(nameandtype_entry.ref2);

        symbol_typet class_symbol=
          java_classname(id2string(class_name_entry.s));

        exprt fieldref("fieldref", type);
        fieldref.set(ID_class, class_symbol.get_identifier());
        fieldref.set(ID_component_name, name_entry.s);

        it->expr=fieldref;
      }
      break;

    case CONSTANT_Methodref:
    case CONSTANT_InterfaceMethodref:
      {
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        const pool_entryt &name_entry=pool_entry(nameandtype_entry.ref1);
        const pool_entryt &class_entry=pool_entry(it->ref1);
        const pool_entryt &class_name_entry=pool_entry(class_entry.ref1);
        typet type=type_entry(nameandtype_entry.ref2);

        symbol_typet class_symbol=
          java_classname(id2string(class_name_entry.s));

        irep_idt component_name=
          id2string(name_entry.s)+
          ":"+id2string(pool_entry(nameandtype_entry.ref2).s);

        irep_idt class_name=
          class_symbol.get_identifier();

        irep_idt identifier=
          id2string(class_name)+"."+id2string(component_name);

        exprt virtual_function(ID_virtual_function, type);
        virtual_function.set(ID_component_name, component_name);
        virtual_function.set(ID_C_class, class_name);
        virtual_function.set(ID_C_base_name, name_entry.s);
        virtual_function.set(ID_identifier, identifier);

        it->expr=virtual_function;
      }
      break;

    case CONSTANT_String:
      {
        // ldc turns these into references to java.lang.String
        exprt string_literal(ID_java_string_literal);
        string_literal.set(ID_value, pool_entry(it->ref1).s);
        it->expr=string_literal;
      }
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
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        typet type=type_entry(nameandtype_entry.ref2);
        it->expr.type()=type;
      }
      break;

    default:{};
    }
  }
}

void java_bytecode_parsert::rinterfaces(classt &parsed_class)
{
  u2 interfaces_count=read_u2();

  for(std::size_t i=0; i<interfaces_count; i++)
    parsed_class.implements
      .push_back(constant(read_u2()).type().get(ID_C_base_name));
}

void java_bytecode_parsert::rfields(classt &parsed_class)
{
  u2 fields_count=read_u2();

  for(std::size_t i=0; i<fields_count; i++)
  {
    fieldt &field=parsed_class.add_field();

    u2 access_flags=read_u2();
    u2 name_index=read_u2();
    u2 descriptor_index=read_u2();
    u2 attributes_count=read_u2();

    field.name=pool_entry(name_index).s;
    field.is_static=(access_flags&ACC_STATIC)!=0;
    field.is_final=(access_flags&ACC_FINAL)!=0;
    field.is_enum=(access_flags&ACC_ENUM)!=0;

    field.descriptor=id2string(pool_entry(descriptor_index).s);
    field.is_public=(access_flags&ACC_PUBLIC)!=0;
    field.is_protected=(access_flags&ACC_PROTECTED)!=0;
    field.is_private=(access_flags&ACC_PRIVATE)!=0;
    size_t flags=(field.is_public?1:0)+
      (field.is_protected?1:0)+
      (field.is_private?1:0);
    assert(flags<=1);

    for(std::size_t j=0; j<attributes_count; j++)
      rfield_attribute(field);
  }
}

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

  u4 address;
  size_t bytecode_index=0; // index of bytecode instruction

  for(address=0; address<code_length; address++)
  {
    bool wide_instruction=false;
    u4 start_of_instruction=address;

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
    instruction.source_location
      .set_java_bytecode_index(std::to_string(bytecode_index));

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
        s1 c=read_u1();
        instruction.args.push_back(from_integer(c, signedbv_typet(8)));
      }
      address+=1;

      break;

    case 'o': // two byte branch offset, signed
      {
        s2 offset=read_u2();
        instruction.args.push_back(
          from_integer(address+offset, signedbv_typet(16)));
      }
      address+=2;
      break;

    case 'O': // four byte branch offset, signed
      {
        s4 offset=read_u4();
        instruction.args.push_back(
          from_integer(address+offset, signedbv_typet(32)));
      }
      address+=4;
      break;

    case 'v': // local variable index (one byte)
      {
        u1 v=read_u1();
        instruction.args.push_back(from_integer(v, unsignedbv_typet(8)));
      }
      address+=1;
      break;

    case 'V':
      // local variable index (two bytes) plus two signed bytes
      if(wide_instruction)
      {
        u2 v=read_u2();
        instruction.args.push_back(from_integer(v, unsignedbv_typet(16)));
        s2 c=read_u2();
        instruction.args.push_back(from_integer(c, signedbv_typet(16)));
        address+=4;
      }
      else // local variable index (one byte) plus one signed byte
      {
        u1 v=read_u1();
        instruction.args.push_back(from_integer(v, unsignedbv_typet(8)));
        s1 c=read_u1();
        instruction.args.push_back(from_integer(c, signedbv_typet(8)));
        address+=2;
      }
      break;

    case 'I': // two byte constant_pool index plus two bytes
      {
        u2 c=read_u2();
        instruction.args.push_back(constant(c));
        u1 b1=read_u1();
        instruction.args.push_back(from_integer(b1, unsignedbv_typet(8)));
        u1 b2=read_u1();
        instruction.args.push_back(from_integer(b2, unsignedbv_typet(8)));
      }
      address+=4;
      break;

    case 'L': // lookupswitch
      {
        u4 base_offset=address;

        // first a pad to 32-bit align
        while(((address+1)&3)!=0) { read_u1(); address++; }

        // now default value
        s4 default_value=read_u4();
        instruction.args.push_back(
          from_integer(base_offset+default_value, signedbv_typet(32)));
        address+=4;

        // number of pairs
        u4 npairs=read_u4();
        address+=4;

        for(std::size_t i=0; i<npairs; i++)
        {
          s4 match=read_u4();
          s4 offset=read_u4();
          instruction.args.push_back(
            from_integer(match, signedbv_typet(32)));
          instruction.args.push_back(
            from_integer(base_offset+offset, signedbv_typet(32)));
          address+=8;
        }
      }
      break;

    case 'T': // tableswitch
      {
        size_t base_offset=address;

        // first a pad to 32-bit align
        while(((address+1)&3)!=0) { read_u1(); address++; }

        // now default value
        s4 default_value=read_u4();
        instruction.args.push_back(
          from_integer(base_offset+default_value, signedbv_typet(32)));
        address+=4;

        // now low value
        s4 low_value=read_u4();
        address+=4;

        // now high value
        s4 high_value=read_u4();
        address+=4;

        // there are high-low+1 offsets, and they are signed
        for(s4 i=low_value; i<=high_value; i++)
        {
          s4 offset=read_u4();
          instruction.args.push_back(from_integer(i, signedbv_typet(32)));
          instruction.args.push_back(
            from_integer(base_offset+offset, signedbv_typet(32)));
          address+=4;
        }
      }
      break;

    case 'm': // multianewarray: constant-pool index plus one unsigned byte
      {
        u2 c=read_u2(); // constant-pool index
        instruction.args.push_back(constant(c));
        u1 dimensions=read_u1(); // number of dimensions
        instruction.args.push_back(
          from_integer(dimensions, unsignedbv_typet(8)));
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
        default:{};
        }
        instruction.args.push_back(type_exprt(t));
      }
      address+=1;
      break;

    case 's': // a signed short
      {
        s2 s=read_u2();
        instruction.args.push_back(from_integer(s, signedbv_typet(16)));
      }
      address+=2;
      break;

    default:
      throw "unknown JVM bytecode instruction";
    }
    bytecode_index++;
  }

  if(address!=code_length)
  {
    error() << "bytecode length mismatch" << eom;
    throw 0;
  }
}

void java_bytecode_parsert::rmethod_attribute(methodt &method)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="Code")
  {
    u2 UNUSED max_stack=read_u2();
    u2 UNUSED max_locals=read_u2();

    rbytecode(method.instructions);

    u2 exception_table_length=read_u2();
    method.exception_table.resize(exception_table_length);

    for(std::size_t e=0; e<exception_table_length; e++)
    {
      u2 start_pc=read_u2();
      u2 end_pc=read_u2();
      u2 handler_pc=read_u2();
      u2 catch_type=read_u2();
      method.exception_table[e].start_pc=start_pc;
      method.exception_table[e].end_pc=end_pc;
      method.exception_table[e].handler_pc=handler_pc;
      if(catch_type!=0)
        method.exception_table[e].catch_type=
          to_symbol_type(pool_entry(catch_type).expr.type());
    }

    u2 attributes_count=read_u2();

    for(std::size_t j=0; j<attributes_count; j++)
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
      it->source_location
        .set_function(
          "java::"+id2string(parse_tree.parsed_class.name)+"."+
          id2string(method.name)+":"+method.descriptor);
    }

    // line number of method
    if(!method.instructions.empty())
      method.source_location.set_line(
        method.instructions.begin()->source_location.get_line());
  }
  else if(attribute_name=="Signature")
  {
    u2 signature_index=read_u2();
    method.signature=id2string(pool_entry(signature_index).s);
  }
  else if(attribute_name=="RuntimeInvisibleAnnotations" ||
          attribute_name=="RuntimeVisibleAnnotations")
  {
    rRuntimeAnnotation_attribute(method.annotations);
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::rfield_attribute(fieldt &field)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="Signature")
  {
    u2 signature_index=read_u2();
    field.signature=id2string(pool_entry(signature_index).s);
  }
  else if(attribute_name=="RuntimeInvisibleAnnotations" ||
     attribute_name=="RuntimeVisibleAnnotations")
  {
    rRuntimeAnnotation_attribute(field.annotations);
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::rcode_attribute(methodt &method)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="LineNumberTable")
  {
    // address -> instructiont
    typedef std::map<unsigned,
                     methodt::instructionst::iterator> instruction_mapt;
    instruction_mapt instruction_map;

    for(methodt::instructionst::iterator
        it=method.instructions.begin();
        it!=method.instructions.end();
        it++)
    {
      instruction_map[it->address]=it;
    }

    u2 line_number_table_length=read_u2();

    for(std::size_t i=0; i<line_number_table_length; i++)
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
  else if(attribute_name=="LocalVariableTable")
  {
    u2 local_variable_table_length=read_u2();

    method.local_variable_table.resize(local_variable_table_length);

    for(std::size_t i=0; i<local_variable_table_length; i++)
    {
      u2 start_pc=read_u2();
      u2 length=read_u2();
      u2 name_index=read_u2();
      u2 descriptor_index=read_u2();
      u2 index=read_u2();

      method.local_variable_table[i].index=index;
      method.local_variable_table[i].name=pool_entry(name_index).s;
      method.local_variable_table[i].descriptor=
        id2string(pool_entry(descriptor_index).s);
      method.local_variable_table[i].start_pc=start_pc;
      method.local_variable_table[i].length=length;
    }
  }
  else if(attribute_name=="LocalVariableTypeTable")
  {
    parse_local_variable_type_table(method);
  }
  else if(attribute_name=="StackMapTable")
  {
    u2 stack_map_entries=read_u2();

    method.stack_map_table.resize(stack_map_entries);

    for(size_t i=0; i<stack_map_entries; i++)
    {
      u1 frame_type=read_u1();
      if(frame_type<=63)
      {
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::SAME;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(0);
      }
      else if(64<=frame_type && frame_type<=127)
      {
        method.stack_map_table[i].type=
          methodt::stack_map_table_entryt::SAME_LOCALS_ONE_STACK;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(1);
        methodt::verification_type_infot verification_type_info;
        read_verification_type_info(verification_type_info);
        method.stack_map_table[i].stack[0]=verification_type_info;
      }
      else if(frame_type==247)
      {
        method.stack_map_table[i].type=
          methodt::stack_map_table_entryt::SAME_LOCALS_ONE_STACK_EXTENDED;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(1);
        methodt::verification_type_infot verification_type_info;
        u2 offset_delta=read_u2();
        read_verification_type_info(verification_type_info);
        method.stack_map_table[i].stack[0]=verification_type_info;
        method.stack_map_table[i].offset_delta=offset_delta;
      }
      else if(248<=frame_type && frame_type<=250)
      {
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::CHOP;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(0);
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
      }
      else if(frame_type==251)
      {
        method.stack_map_table[i].type
          =methodt::stack_map_table_entryt::SAME_EXTENDED;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(0);
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
      }
      else if(252<=frame_type && frame_type<=254)
      {
        size_t new_locals=(size_t) (frame_type-251);
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::APPEND;
        method.stack_map_table[i].locals.resize(new_locals);
        method.stack_map_table[i].stack.resize(0);
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
        for(size_t k=0; k<new_locals; k++)
        {
          method.stack_map_table[i].locals
            .push_back(methodt::verification_type_infot());
          methodt::verification_type_infot &v=
            method.stack_map_table[i].locals.back();
          read_verification_type_info(v);
        }
      }
      else if(frame_type==255)
      {
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::FULL;
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
        u2 number_locals=read_u2();
        method.stack_map_table[i].locals.resize(number_locals);
        for(size_t k=0; k<(size_t) number_locals; k++)
        {
          method.stack_map_table[i].locals
            .push_back(methodt::verification_type_infot());
          methodt::verification_type_infot &v=
            method.stack_map_table[i].locals.back();
          read_verification_type_info(v);
        }
        u2 number_stack_items=read_u2();
        method.stack_map_table[i].stack.resize(number_stack_items);
        for(size_t k=0; k<(size_t) number_stack_items; k++)
        {
          method.stack_map_table[i].stack
            .push_back(methodt::verification_type_infot());
          methodt::verification_type_infot &v=
            method.stack_map_table[i].stack.back();
          read_verification_type_info(v);
        }
      }
      else
        throw "error: unknown stack frame type encountered";
    }
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::read_verification_type_info(
  methodt::verification_type_infot &v)
{
  u1 tag=read_u1();
  switch(tag)
  {
  case VTYPE_INFO_TOP:
    v.type=methodt::verification_type_infot::TOP;
    break;
  case VTYPE_INFO_INTEGER:
    v.type=methodt::verification_type_infot::INTEGER;
    break;
  case VTYPE_INFO_FLOAT:
    v.type=methodt::verification_type_infot::FLOAT;
    break;
  case VTYPE_INFO_LONG:
    v.type=methodt::verification_type_infot::LONG;
    break;
  case VTYPE_INFO_DOUBLE:
    v.type=methodt::verification_type_infot::DOUBLE;
    break;
  case VTYPE_INFO_ITEM_NULL:
    v.type=methodt::verification_type_infot::ITEM_NULL;
    break;
  case VTYPE_INFO_UNINIT_THIS:
    v.type=methodt::verification_type_infot::UNINITIALIZED_THIS;
    break;
  case VTYPE_INFO_OBJECT:
    v.type=methodt::verification_type_infot::OBJECT;
    v.cpool_index=read_u2();
    break;
  case VTYPE_INFO_UNINIT:
    v.type=methodt::verification_type_infot::UNINITIALIZED;
    v.offset=read_u2();
    break;
  default:
    throw "error: unknown verification type info encountered";
  }
}

void java_bytecode_parsert::rRuntimeAnnotation_attribute(
  annotationst &annotations)
{
  u2 num_annotations=read_u2();

  for(u2 number=0; number<num_annotations; number++)
  {
    annotationt annotation;
    rRuntimeAnnotation(annotation);
    annotations.push_back(annotation);
  }
}

void java_bytecode_parsert::rRuntimeAnnotation(
  annotationt &annotation)
{
  u2 type_index=read_u2();
  annotation.type=type_entry(type_index);
  relement_value_pairs(annotation.element_value_pairs);
}

void java_bytecode_parsert::relement_value_pairs(
  annotationt::element_value_pairst &element_value_pairs)
{
  u2 num_element_value_pairs=read_u2();
  element_value_pairs.resize(num_element_value_pairs);

  for(auto &element_value_pair : element_value_pairs)
  {
    u2 element_name_index=read_u2();
    element_value_pair.element_name=pool_entry(element_name_index).s;

    relement_value_pair(element_value_pair);
  }
}

void java_bytecode_parsert::relement_value_pair(
  annotationt::element_value_pairt &element_value_pair)
{
  u1 tag=read_u1();

  switch(tag)
  {
  case 'e':
    {
      UNUSED u2 type_name_index=read_u2();
      UNUSED u2 const_name_index=read_u2();
      // todo: enum
    }
    break;

  case 'c':
    {
      UNUSED u2 class_info_index=read_u2();
      // todo: class
    }
    break;

  case '@':
    {
      // another annotation, recursively
      annotationt annotation;
      rRuntimeAnnotation(annotation);
    }
    break;

  case '[':
    {
      u2 num_values=read_u2();
      for(std::size_t i=0; i<num_values; i++)
      {
        annotationt::element_value_pairt element_value;
        relement_value_pair(element_value); // recursive call
      }
    }
    break;

  case 's':
    {
      u2 const_value_index=read_u2();
      element_value_pair.value=string_constantt(
        pool_entry(const_value_index).s);
    }
    break;

  default:
    {
      u2 const_value_index=read_u2();
      element_value_pair.value=constant(const_value_index);
    }

  break;
  }
}

void java_bytecode_parsert::rclass_attribute(classt &parsed_class)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="SourceFile")
  {
    u2 sourcefile_index=read_u2();
    irep_idt sourcefile_name;

    std::string fqn(id2string(parsed_class.name));
    size_t last_index=fqn.find_last_of(".");
    if(last_index==std::string::npos)
      sourcefile_name=pool_entry(sourcefile_index).s;
    else
    {
      std::string package_name=fqn.substr(0, last_index+1);
      std::replace(package_name.begin(), package_name.end(), '.', '/');
      const std::string &full_file_name=
        package_name+id2string(pool_entry(sourcefile_index).s);
      sourcefile_name=full_file_name;
    }

    for(methodst::iterator m_it=parsed_class.methods.begin();
        m_it!=parsed_class.methods.end();
        m_it++)
    {
      m_it->source_location.set_file(sourcefile_name);
      for(instructionst::iterator i_it=m_it->instructions.begin();
          i_it!=m_it->instructions.end();
          i_it++)
      {
        if(!i_it->source_location.get_line().empty())
          i_it->source_location.set_file(sourcefile_name);
      }
    }
  }
  else if(attribute_name=="Signature")
  {
    u2 signature_index=read_u2();
    parsed_class.signature=id2string(pool_entry(signature_index).s);
  }
  else if(attribute_name=="RuntimeInvisibleAnnotations" ||
          attribute_name=="RuntimeVisibleAnnotations")
  {
    rRuntimeAnnotation_attribute(parsed_class.annotations);
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::rmethods(classt &parsed_class)
{
  u2 methods_count=read_u2();

  for(std::size_t j=0; j<methods_count; j++)
    rmethod(parsed_class);
}

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

  method.is_final=(access_flags&ACC_FINAL)!=0;
  method.is_static=(access_flags&ACC_STATIC)!=0;
  method.is_abstract=(access_flags&ACC_ABSTRACT)!=0;
  method.is_public=(access_flags&ACC_PUBLIC)!=0;
  method.is_protected=(access_flags&ACC_PROTECTED)!=0;
  method.is_private=(access_flags&ACC_PRIVATE)!=0;
  method.is_synchronized=(access_flags&ACC_SYNCHRONIZED)!=0;
  method.is_native=(access_flags&ACC_NATIVE)!=0;
  method.name=pool_entry(name_index).s;
  method.base_name=pool_entry(name_index).s;
  method.descriptor=id2string(pool_entry(descriptor_index).s);

  size_t flags=(method.is_public?1:0)+
    (method.is_protected?1:0)+
    (method.is_private?1:0);
  assert(flags<=1);
  u2 attributes_count=read_u2();

  for(std::size_t j=0; j<attributes_count; j++)
    rmethod_attribute(method);
}

bool java_bytecode_parse(
  std::istream &istream,
  java_bytecode_parse_treet &parse_tree,
  message_handlert &message_handler)
{
  java_bytecode_parsert java_bytecode_parser;
  java_bytecode_parser.in=&istream;
  java_bytecode_parser.set_message_handler(message_handler);

  bool parser_result=java_bytecode_parser.parse();

  parse_tree.swap(java_bytecode_parser.parse_tree);

  return parser_result;
}

bool java_bytecode_parse(
  const std::string &file,
  java_bytecode_parse_treet &parse_tree,
  message_handlert &message_handler)
{
  std::ifstream in(file, std::ios::binary);

  if(!in)
  {
    messaget message(message_handler);
    message.error() << "failed to open input file `"
                    << file << '\'' << messaget::eom;
    return true;
  }

  return java_bytecode_parse(in, parse_tree, message_handler);
}

/// Parses the local variable type table of a method. The LVTT holds generic
/// type information for variables in the local variable table (LVT). At most as
/// many variables as present in the LVT can be in the LVTT.
void java_bytecode_parsert::parse_local_variable_type_table(methodt &method)
{
  u2 local_variable_type_table_length=read_u2();

  INVARIANT(
    local_variable_type_table_length<=method.local_variable_table.size(),
    "Local variable type table cannot have more elements "
    "than the local variable table.");
  for(std::size_t i=0; i<local_variable_type_table_length; i++)
  {
    u2 start_pc=read_u2();
    u2 length=read_u2();
    u2 name_index=read_u2();
    u2 signature_index=read_u2();
    u2 index=read_u2();

    bool found=false;
    for(auto &lvar : method.local_variable_table)
    {
      // compare to entry in LVT
      if(lvar.index==index &&
         lvar.name==pool_entry(name_index).s &&
         lvar.start_pc==start_pc &&
         lvar.length==length)
      {
        found=true;
        lvar.signature=id2string(pool_entry(signature_index).s);
        break;
      }
    }
    INVARIANT(
      found,
      "Entry in LocalVariableTypeTable must be present in LVT");
  }
}
