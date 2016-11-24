#include <util/std_code.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/i2string.h>
#include <util/string2int.h>

#include "c_types.h"

#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

#define mto(x, y) stack(x).move_to_operands(stack(y))
#define mts(x, y) (stack_type(x).move_to_subtypes(stack_type(y)))
#define binary(x, y, l, id, z) { init(x, id); \
  stack(x).add_source_location()=stack(l).source_location(); \
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

  if(dest.is_nil())
  {
    dest=src;
    return;
  }

  if(dest.id()!=ID_merged_type)
  {
    source_locationt location=static_cast<const exprt &>(dest).source_location();
    typet new_type(ID_merged_type);
    new_type.move_to_subtypes((typet &)(dest));
    dest.swap(new_type);
    static_cast<exprt &>(dest).add_source_location()=location;
  }

  static_cast<typet &>(dest).move_to_subtypes(static_cast<typet &>(src));
}

/*******************************************************************\

Function: merge_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
static void merge_types(const YYSTYPE dest, const YYSTYPE src)
{
  merge_types(stack(dest), stack(src));
}
#endif

/*******************************************************************\

Function: merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static YYSTYPE merge(const YYSTYPE src1, const YYSTYPE src2)
{
  merge_types(stack(src1), stack(src2));
  return src1;
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
         src.id()==ID_c_bit_field);

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
  make_subtype(stack_type(dest), stack_type(src));
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
  stack_type(dest).subtype()=typet(ID_abstract);
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

Function: create_function_scope

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void create_function_scope(const YYSTYPE d)
{
  ansi_c_declarationt &declaration=to_ansi_c_declaration(stack(d));
  ansi_c_declaratort &declarator=declaration.declarator();

  irep_idt function_name=declarator.get_base_name();

  // record which function we are in
  PARSER.set_function(function_name);

  std::string prefix=PARSER.current_scope().prefix+
                     id2string(function_name)+"::";
  PARSER.new_scope(prefix);

  // The grammar doesn't actually enforce that a function type
  // is used to define a function body. We will complain in the
  // type checker about it.
  if(declarator.type().id()==ID_code)
  {
    code_typet &code_type=to_code_type(declarator.type());
    
    code_typet::parameterst &parameters=code_type.parameters();
    
    // Add the parameter declarations to the scope.
    for(code_typet::parameterst::iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      if(it->id()==ID_declaration)
      {
        ansi_c_declarationt &param_decl=to_ansi_c_declaration(*it);

        // we record the function name in the location
        param_decl.add_source_location().set_function(function_name);
       
        if(!param_decl.declarators().empty())
        {
          // add to scope
          PARSER.current_scope().name_map
            [param_decl.declarator().get_base_name()].id_class=ANSI_C_SYMBOL;
        }
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

static void adjust_KnR_parameters(
  irept &parameters,
  exprt &declarations)
{
  // the below is probably better done in the type checker

  Forall_operands(d_it, declarations)
  {
    assert(d_it->id()==ID_declaration);
    ansi_c_declarationt &declaration=
      to_ansi_c_declaration(static_cast<exprt &>(*d_it));

    // Go over declarators
    ansi_c_declarationt::declaratorst &declarators=
      declaration.declarators();

    for(ansi_c_declarationt::declaratorst::const_iterator
        it=declarators.begin();
        it!=declarators.end();
        it++)
    {
      irep_idt base_name=it->get_base_name();

      // we just do a linear search over the parameters
      // this could be improved with a hash map
      Forall_irep(a_it, parameters.get_sub())
      {
        ansi_c_declarationt &p_decl=
          to_ansi_c_declaration(static_cast<exprt &>(*a_it));

        if(p_decl.declarator().get_base_name()==base_name)
        {
          // match
          // This copies the declaration type, which can be a
          // problem if there are compound bodies in there.
          p_decl.type()=declaration.type();
          p_decl.declarator().type()=it->type();
          break;
        }
      }
    }
  }
}
