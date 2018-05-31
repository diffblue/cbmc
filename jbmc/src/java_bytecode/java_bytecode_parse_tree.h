/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSE_TREE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSE_TREE_H

#include <set>
#include <map>

#include <util/optional.h>
#include <util/std_code.h>
#include <util/std_types.h>

#include "bytecode_info.h"

class java_bytecode_parse_treet
{
public:
  // Disallow copy construction and copy assignment, but allow move construction
  // and move assignment.
  #ifndef _MSC_VER // Ommit this on MS VC2013 as move is not supported.
  java_bytecode_parse_treet(const java_bytecode_parse_treet &) = delete;
  java_bytecode_parse_treet &
  operator=(const java_bytecode_parse_treet &) = delete;
  java_bytecode_parse_treet(java_bytecode_parse_treet &&) = default;
  java_bytecode_parse_treet &operator=(java_bytecode_parse_treet &&) = default;
  #endif

  virtual ~java_bytecode_parse_treet() = default;
  class annotationt
  {
  public:
    typet type;

    class element_value_pairt
    {
    public:
      irep_idt element_name;
      exprt value;
      void output(std::ostream &) const;
    };

    typedef std::vector<element_value_pairt> element_value_pairst;
    element_value_pairst element_value_pairs;

    void output(std::ostream &) const;
  };

  typedef std::vector<annotationt> annotationst;

  static optionalt<annotationt> find_annotation(
    const annotationst &annotations,
    const irep_idt &annotation_type_name);

  class instructiont
  {
  public:
    source_locationt source_location;
    unsigned address;
    irep_idt statement;
    typedef std::vector<exprt> argst;
    argst args;
  };

  class membert
  {
  public:
    std::string descriptor;
    optionalt<std::string> signature;
    irep_idt name;
    bool is_public, is_protected, is_private, is_static, is_final;
    annotationst annotations;

    virtual void output(std::ostream &out) const = 0;

    membert():
      is_public(false), is_protected(false),
      is_private(false), is_static(false), is_final(false)
    {
    }
  };

  class methodt:public membert
  {
  public:
    irep_idt base_name;
    bool is_native, is_abstract, is_synchronized;
    source_locationt source_location;

    typedef std::vector<instructiont> instructionst;
    instructionst instructions;

    instructiont &add_instruction()
    {
      instructions.push_back(instructiont());
      return instructions.back();
    }

    struct exceptiont
    {
    public:
      exceptiont()
        : start_pc(0), end_pc(0), handler_pc(0), catch_type(irep_idt())
      {
      }

      std::size_t start_pc;
      std::size_t end_pc;
      std::size_t handler_pc;
      symbol_typet catch_type;
    };

    typedef std::vector<exceptiont> exception_tablet;
    exception_tablet exception_table;

    class local_variablet
    {
    public:
      irep_idt name;
      std::string descriptor;
      optionalt<std::string> signature;
      std::size_t index;
      std::size_t start_pc;
      std::size_t length;
    };

    typedef std::vector<local_variablet> local_variable_tablet;
    local_variable_tablet local_variable_table;

    class verification_type_infot
    {
    public:
      enum verification_type_info_type { TOP, INTEGER, FLOAT, LONG, DOUBLE,
                                         ITEM_NULL, UNINITIALIZED_THIS,
                                         OBJECT, UNINITIALIZED};
      verification_type_info_type type;
      u1 tag;
      u2 cpool_index;
      u2 offset;
    };

    class stack_map_table_entryt
    {
    public:
      enum stack_frame_type
      {
        SAME, SAME_LOCALS_ONE_STACK, SAME_LOCALS_ONE_STACK_EXTENDED,
        CHOP, SAME_EXTENDED, APPEND, FULL
      };
      stack_frame_type type;
      size_t offset_delta;
      size_t chops;
      size_t appends;

      typedef std::vector<verification_type_infot>
        local_verification_type_infot;
      typedef std::vector<verification_type_infot>
        stack_verification_type_infot;

      local_verification_type_infot locals;
      stack_verification_type_infot stack;
    };

    typedef std::vector<stack_map_table_entryt> stack_map_tablet;
    stack_map_tablet stack_map_table;

    virtual void output(std::ostream &out) const;

    methodt():
      is_native(false),
      is_abstract(false),
      is_synchronized(false)
    {
    }

    virtual ~methodt() = default;
  };

  class fieldt:public membert
  {
  public:
    virtual ~fieldt() = default;
    virtual void output(std::ostream &out) const;
    bool is_enum;
  };

  class classt
  {
  public:
    classt() = default;

    // Disallow copy construction and copy assignment, but allow move
    // construction and move assignment.
    #ifndef _MSC_VER // Ommit this on MS VC2013 as move is not supported.
    classt(const classt &) = delete;
    classt &operator=(const classt &) = delete;
    classt(classt &&) = default;
    classt &operator=(classt &&) = default;
    #endif

    irep_idt name, extends;
    bool is_abstract=false;
    bool is_enum=false;
    bool is_public=false, is_protected=false, is_private=false;
    bool is_final = false;
    bool attribute_bootstrapmethods_read = false;
    size_t enum_elements=0;

    enum class method_handle_typet
    {
      LAMBDA_METHOD_HANDLE,
      UNKNOWN_HANDLE
    };

    typedef std::vector<u2> u2_valuest;
    class lambda_method_handlet
    {
    public:
      method_handle_typet handle_type;
      irep_idt lambda_method_name;
      irep_idt lambda_method_ref;
      irep_idt interface_type;
      irep_idt method_type;
      u2_valuest u2_values;
      lambda_method_handlet() : handle_type(method_handle_typet::UNKNOWN_HANDLE)
      {
      }

      static lambda_method_handlet
      create_unknown_handle(const u2_valuest params)
      {
        lambda_method_handlet lambda_method_handle;
        lambda_method_handle.handle_type = method_handle_typet::UNKNOWN_HANDLE;
        lambda_method_handle.u2_values = std::move(params);
        return lambda_method_handle;
      }

      bool is_unknown_handle() const
      {
        return handle_type == method_handle_typet::UNKNOWN_HANDLE;
      }
    };

    // TODO(tkiley): This map shouldn't be interacted with directly (instead
    // TODO(tkiley): using add_method_handle and get_method_handle and instead
    // TODO(tkiley): should be made private. TG-2785
    typedef std::map<std::pair<irep_idt, size_t>, lambda_method_handlet>
      lambda_method_handle_mapt;
    lambda_method_handle_mapt lambda_method_handle_map;

    typedef std::list<irep_idt> implementst;
    implementst implements;
    optionalt<std::string> signature;
    typedef std::list<fieldt> fieldst;
    typedef std::list<methodt> methodst;
    fieldst fields;
    methodst methods;
    annotationst annotations;

    fieldt &add_field()
    {
      fields.push_back(fieldt());
      return fields.back();
    }

    methodt &add_method()
    {
      methods.push_back(methodt());
      return methods.back();
    }

    void add_method_handle(size_t bootstrap_index, lambda_method_handlet handle)
    {
      lambda_method_handle_map[{name, bootstrap_index}] = handle;
    }

    const lambda_method_handlet &get_method_handle(size_t bootstrap_index) const
    {
      return lambda_method_handle_map.at({name, bootstrap_index});
    }

    void output(std::ostream &out) const;

  };

  classt parsed_class;


  void output(std::ostream &out) const;

  typedef std::set<irep_idt> class_refst;
  class_refst class_refs;

  bool loading_successful;

  java_bytecode_parse_treet():loading_successful(false)
  {
  }
};

/// Represents the argument of an instruction that uses a CONSTANT_Fieldref
/// This is used for example as an argument to a getstatic and putstatic
/// instruction
class fieldref_exprt : public exprt
{
public:
  fieldref_exprt(
    const typet &type,
    const irep_idt &component_name,
    const irep_idt &class_name)
    : exprt(ID_empty_string, type)
  {
    set(ID_class, class_name);
    set(ID_component_name, component_name);
  }
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSE_TREE_H
