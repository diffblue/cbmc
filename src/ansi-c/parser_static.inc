#include <cstdlib>

#include <util/std_code.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/i2string.h>

#include "c_types.h"

#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

#define mto(x, y) stack(x).move_to_operands(stack(y))
#define mts(x, y) ((typet &)stack(x)).move_to_subtypes((typet &)stack(y))
#define binary(x, y, l, id, z) { init(x, id); \
  stack(x).location()=stack(l).location(); \
  stack(x).reserve_operands(2); mto(x, y); mto(x, z); }

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void init(YYSTYPE &expr)
{
  newstack(expr);
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void init(YYSTYPE &expr, const irep_idt &id)
{
  newstack(expr);
  stack(expr).id(id);
}

/*******************************************************************\

Function: set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void set(YYSTYPE expr, const irep_idt &id)
{
  stack(expr).id(id);
}

/*******************************************************************\

Function: statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void statement(YYSTYPE &expr, const irep_idt &id)
{
  set(expr, ID_code);
  stack(expr).type().id(ID_code);
  stack(expr).set(ID_statement, id);
}

/*******************************************************************\

Function: decl_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void decl_statement(
  YYSTYPE &dest,
  YYSTYPE &decl,
  YYSTYPE &initializer)
{
  ansi_c_declarationt &ansi_c_declaration=
    to_ansi_c_declaration(stack(decl));

  codet decl_statement(ID_decl);
  
  symbol_exprt symbol;
  symbol.set_identifier(ansi_c_declaration.get_name());
  
  decl_statement.move_to_operands(symbol);
  
  if(stack(initializer).is_not_nil())
  {
    // repeat declaration to set the initializer
    ansi_c_declaration.value()=stack(initializer);
    PARSER.copy_item(ansi_c_declaration);
  
    decl_statement.move_to_operands(stack(initializer));
  }
  
  stack(dest).move_to_operands(decl_statement);
}

/*******************************************************************\

Function: merge_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void merge_types(irept &dest, irept &src)
{
  #if 0
  std::cout << "D: " << dest.pretty() << std::endl;
  std::cout << "S: " << src.pretty() << std::endl;
  #endif

  if(src.is_nil())
    return;

  if(dest.id()!=ID_merged_type)
  {
    locationt location=static_cast<const exprt &>(dest).location();
    typet new_type(ID_merged_type);
    new_type.move_to_subtypes((typet &)(dest));
    dest.swap(new_type);
    static_cast<exprt &>(dest).location()=location;
  }

  static_cast<typet &>(dest).move_to_subtypes(static_cast<typet &>(src));
}

/*******************************************************************\

Function: merge_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void merge_types(const YYSTYPE dest, const YYSTYPE src)
{
  merge_types(stack(dest), stack(src));
}

/*******************************************************************\

Function: make_subtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void make_subtype(typet &dest, typet &src)
{  
  // inserts "src" into "dest"
  // e.g., src is a pointer or array,
  // dest is a symbol or type
  
  // find spot in 'dest' where to insert 'src'
  
  #if 0
  std::cout << "D: " << dest.pretty() << std::endl;
  std::cout << "S: " << src.pretty() << std::endl;
  #endif
  
  assert(src.id()==ID_array ||
         src.id()==ID_pointer ||
         src.id()==ID_code ||
         src.id()==ID_merged_type ||
         src.id()==ID_c_bitfield);

  typet *p=&dest;

  while(true)
  {
    // see if we need to walk down
    typet *sub=p;
    
    if(p->id()==ID_merged_type)
    {
      // do last one
      assert(!p->subtypes().empty());
      sub=&(p->subtypes().back());
    }

    if(sub->id()==ID_pointer ||
       sub->id()==ID_array ||
       sub->id()==ID_code)
    {
      // walk down
      p=&sub->subtype();    
    }
    else
    {
      if(p->id()==ID_abstract)
      {
        p->swap(src);
        break;
      }
      else if(p->is_nil())
        assert(false);
      else if(p->id()==irep_idt())
        assert(false);
      else
      {
        // *p is now type or symbol
    
        // save symbol
        typet symbol=*p;
        p->swap(src);
      
        // find spot where to put symbol
        while(true)
        {
          if(p->id()==ID_abstract)
          {
            p->swap(symbol);
            break;
          }
          else if(p->id()==ID_merged_type)
          {
            assert(!p->subtypes().empty());
            p=&(p->subtypes().back());
          }
          else if(p->id()==irep_idt())
            assert(false);
          else if(p->is_nil())
            assert(false);
          else
            p=&p->subtype();
        }
        break;
      }
    }
  }
}

/*******************************************************************\

Function: make_subtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void make_subtype(YYSTYPE dest, YYSTYPE src)
{
  make_subtype((typet &)stack(dest), (typet &)stack(src));
}
    
/*******************************************************************\

Function: make_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void make_pointer(const YYSTYPE dest)
{
  set(dest, ID_pointer);
  stack(dest).add(ID_subtype)=irept(ID_abstract);
}

/*******************************************************************\

Function: do_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void do_pointer(const YYSTYPE ptr, const YYSTYPE dest)
{
  make_pointer(ptr);
  make_subtype(dest, ptr);
}

/*******************************************************************\

Function: do_enum_members

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void do_enum_members(
  const typet &enum_type,
  exprt &members)
{  
  exprt value;

  // This assigns increasing values to enum constants
  // that do not have an explicit value. We start with 0.
  // In C, enum constants always have type "int".
  value=gen_zero(::enum_type());

  Forall_operands(it, members)
  {
    ansi_c_declarationt &ansi_c_declaration=
      to_ansi_c_declaration(*it);

    exprt &v=ansi_c_declaration.value();
    if(v.is_nil())
      v=value;

    exprt symbol_expr(ID_symbol);
    symbol_expr.set(ID_identifier, ansi_c_declaration.get_name());
    
    value=exprt(ID_plus);
    value.copy_to_operands(symbol_expr, gen_one(::enum_type()));
    
    PARSER.copy_item(ansi_c_declaration);
  }
}

/*******************************************************************\

Function: do_tag

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void do_tag(YYSTYPE &key, YYSTYPE &tag)
{
  irep_idt id_class_str=stack(tag).get(ID_C_id_class);

  ansi_c_id_classt id_class=
    (ansi_c_id_classt)atoi(id_class_str.c_str());

  if(id_class==ANSI_C_TAG) // we have it already
    return;

  // it's new
  ansi_c_declarationt declaration;
  PARSER.new_declaration(stack(key), stack(tag), declaration, ansi_c_parsert::TAG);

  // grab symbol
  stack(tag).id(ID_symbol);
  stack(tag).set(ID_identifier, declaration.get_name());
  stack(tag).location()=declaration.location();

  declaration.type().id("incomplete_"+declaration.type().id_string());
  PARSER.copy_item(declaration);                    
}

/*******************************************************************\

Function: create_function_scope

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

static void create_function_scope(exprt &expr)
{
  ansi_c_declarationt &declaration=to_ansi_c_declaration(expr);

  PARSER.function=declaration.get_base_name();

  std::string prefix=PARSER.current_scope().prefix+
                     id2string(declaration.get_base_name())+"::";
  PARSER.new_scope(prefix);
  
  if(declaration.type().id()==ID_code)
  {
    code_typet &code_type=to_code_type(declaration.type());
    
    code_typet::parameterst &parameters=code_type.parameters();
    
    unsigned anon_count=0;
    
    // do the parameter declarations
    for(code_typet::parameterst::iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      if(it->id()==ID_declaration)
      {
        ansi_c_declarationt &param_decl=to_ansi_c_declaration(*it);

        // we record the function name in the location
        param_decl.location().set_function(declaration.get_base_name());
       
        // make sure we know it's a parameter
        param_decl.set_is_parameter(true);

        if(param_decl.get_base_name()==irep_idt())
        {
          param_decl.set_base_name("#anon_param"+i2string(anon_count++));
          param_decl.set_name(prefix+id2string(param_decl.get_base_name()));
        }
        else
        {
          // add to scope
          PARSER.current_scope().name_map
            [param_decl.get_base_name()].id_class=ANSI_C_SYMBOL;
        }

        // copy declaration
        PARSER.copy_item(param_decl);        
      }
    }
  }
}

/*******************************************************************\

Function: adjust_KnR_parameters

  Inputs:

 Outputs:

 Purpose: this patches the KnR parameter types into the
          function type

\*******************************************************************/

static void adjust_KnR_parameters(irept &parameters, irept &declarations)
{
  Forall_irep(d_it, declarations.get_sub())
  {
    assert(d_it->id()==ID_declaration);
    irep_idt base_name=d_it->get(ID_base_name);

    // we just do a linear search over the parameters
    // this could be improved with a hash map
    Forall_irep(a_it, parameters.get_sub())
    {
      if(a_it->get(ID_base_name)==base_name)
      {
        a_it->add(ID_type)=d_it->find(ID_type);
        break;
      }
    }
  }
}
