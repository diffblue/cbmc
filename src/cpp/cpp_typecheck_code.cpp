/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <i2string.h>
#include <expr_util.h>
#include <location.h>

#include "cpp_typecheck.h"
#include "cpp_convert_type.h"
#include "cpp_declarator_converter.h"
#include "cpp_template_type.h"
#include "cpp_util.h"
#include "cpp_exception_id.h"

/*******************************************************************\

Function: cpp_typecheckt::typecheck_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_code(codet &code)
{
  const irep_idt &statement=code.get(ID_statement);

  if(statement==ID_catch)
  {
    code.type()=code_typet();
    typecheck_catch(code);
  }
  else if(statement==ID_member_initializer)
  {
    code.type()=code_typet();
    typecheck_member_initializer(code);
  }
  else if(statement==ID_msc_if_exists ||
          statement==ID_msc_if_not_exists)
  {
  }
  else
    c_typecheck_baset::typecheck_code(code);
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_catch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_catch(codet &code)
{
  codet::operandst &operands=code.operands();

  for(codet::operandst::iterator
      it=operands.begin();
      it!=operands.end();
      it++)
  {
    code_blockt &block=to_code_block(to_code(*it));

    typecheck_code(block);

    // is it a catch block?
    if(it!=operands.begin())
    {
      const code_blockt &code_block=to_code_block(block);
      assert(code_block.operands().size()>=1);
      const codet &first_instruction=to_code(code_block.op0());
      assert(first_instruction.get_statement()==ID_decl);

      // get the declaration
      const code_declt &code_decl=to_code_decl(first_instruction);

      // get the type
      const typet &type=code_decl.op0().type();
      
      // annotate exception ID
      it->set(ID_exception_id, cpp_exception_id(type, *this));
    }
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_member_initializer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_member_initializer(codet &code)
{
  const cpp_namet &member=
    to_cpp_name(code.find(ID_member));
    
  // Let's first typecheck the operands.
  Forall_operands(it, code)
    typecheck_expr(*it);
    
  // The initializer may be a data member (non-type)
  // or a parent class (type).
  // We ask for VAR only, as we get the parent classes via their
  // constructor!
  cpp_typecheck_fargst fargs;
  fargs.in_use=true;
  fargs.operands=code.operands();

  // We should only really resolve in qualified mode,
  // no need to look into the parent.
  // Plus, this should happen in class scope, not the scope of
  // the constructor because of the constructor arguments.
  exprt symbol_expr=
    resolve(member, cpp_typecheck_resolvet::VAR, fargs);

  if(symbol_expr.type().id()==ID_code)
  {
    const code_typet &code_type=to_code_type(symbol_expr.type());
    
    assert(code_type.arguments().size()>=1);
  
    // It's a parent. Call the constructor that we got.
    side_effect_expr_function_callt function_call;
    
    function_call.function()=symbol_expr;
    function_call.location()=code.location();
    function_call.arguments().reserve(code.operands().size()+1);

    // we have to add 'this'
    exprt this_expr = cpp_scopes.current_scope().this_expr;
    assert(this_expr.is_not_nil());
  
    make_ptr_typecast(
      this_expr,
      code_type.arguments().front().type());

    function_call.arguments().push_back(this_expr);
    
    forall_operands(it, code)
      function_call.arguments().push_back(*it);
      
    // done building the expression, check the argument types
    typecheck_function_call_arguments(function_call);

    if(symbol_expr.get_bool("#not_accessible"))
    {
      irep_idt access = symbol_expr.get(ID_C_access);

      assert(access==ID_private ||
             access==ID_protected ||
             access=="noaccess");

      if(access==ID_private || access=="noaccess")
      {
        #if 0
        err_location(code.location());
        str << "error: constructor of `"
            << to_string(symbol_expr)
            << "' is not accessible";
        throw 0;
        #endif
      }
    }
    
    code_expressiont code_expression;
    code_expression.expression()=function_call;

    code.swap(code_expression);
  }
  else
  {
    // a reference member
    if(symbol_expr.id() == ID_dereference &&
       symbol_expr.op0().id() == ID_member &&
       symbol_expr.get_bool(ID_C_implicit) == true)
    {
      // treat references as normal pointers
      exprt tmp = symbol_expr.op0();
      symbol_expr.swap(tmp);
    }

    if(symbol_expr.id() == ID_symbol &&
       symbol_expr.type().id()!=ID_code)
    {
      // maybe the name of the member collides with a parameter of the constructor
      symbol_expr.make_nil();
      cpp_typecheck_fargst fargs;
      exprt dereference(ID_dereference, cpp_scopes.current_scope().this_expr.type().subtype());
      dereference.copy_to_operands(cpp_scopes.current_scope().this_expr);
      fargs.add_object(dereference);

      {
        cpp_save_scopet cpp_saved_scope(cpp_scopes);
        cpp_scopes.go_to(*(cpp_scopes.id_map[cpp_scopes.current_scope().class_identifier]));
        symbol_expr=resolve(member, cpp_typecheck_resolvet::VAR, fargs);
      }

      if(symbol_expr.id() == ID_dereference &&
         symbol_expr.op0().id() == ID_member &&
         symbol_expr.get_bool(ID_C_implicit) == true)
      {
        // treat references as normal pointers
        exprt tmp = symbol_expr.op0();
        symbol_expr.swap(tmp);
      }
    }

    if(symbol_expr.id() == ID_member &&
       symbol_expr.op0().id() == ID_dereference &&
       symbol_expr.op0().op0() == cpp_scopes.current_scope().this_expr)
    {
      if(is_reference(symbol_expr.type()))
      {
        // it's a reference member
        if(code.operands().size()!= 1)
        {
          err_location(code);
          str << " reference `"+to_string(symbol_expr)+"' expects one initializer";
          throw 0;
        }

        reference_initializer(code.op0(), symbol_expr.type());

        // assign the pointers
        symbol_expr.type().remove("#reference");
        symbol_expr.set("#lvalue", true);
        code.op0().type().remove("#reference");

        side_effect_exprt assign(ID_assign);
        assign.location() = code.location();
        assign.copy_to_operands(symbol_expr, code.op0());
        typecheck_side_effect_assignment(assign);
        code_expressiont new_code;
        new_code.expression()=assign;
        code.swap(new_code);
      }
      else
      {
        // it's a data member
        already_typechecked(symbol_expr);
        
        Forall_operands(it, code)
          already_typechecked(*it);

        exprt call=
          cpp_constructor(code.location(), symbol_expr, code.operands());

        if(call.is_nil())
        {
          call=codet(ID_skip);
          call.location()=code.location();
        }

        code.swap(call);
      }
    }
    else
    {
      err_location(code);
      str << "invalid member initializer `" << to_string(symbol_expr) << "'";
      throw 0;
    }
  }
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_decl(codet &code)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "declaration expected to have one operand";
  }

  assert(code.op0().id()==ID_cpp_declaration);

  cpp_declarationt &declaration=
    to_cpp_declaration(code.op0());
    
  typet &type=declaration.type();
    
  bool is_typedef=convert_typedef(type);

  typecheck_type(type);
  assert(type.is_not_nil());

  if(declaration.declarators().empty() &&
     follow(type).get_bool("#is_anonymous"))
  {
    if(follow(type).id()!=ID_union)
    {
      err_location(code);
      throw "declaration statement does not declare anything";
    }

    convert_anonymous_union(declaration, code);
    return;
  }

  codet new_code(ID_decl_block);
  new_code.reserve_operands(declaration.declarators().size());

  // Do the declarators (optional).
  Forall_cpp_declarators(it, declaration)
  {
    cpp_declaratort &declarator=*it;
    cpp_declarator_convertert cpp_declarator_converter(*this);
    cpp_declarator_converter.is_typedef=is_typedef;

    const symbolt &symbol=
      cpp_declarator_converter.convert(declaration, declarator);

    if(is_typedef) continue;

    codet decl_statement(ID_decl);
    decl_statement.reserve_operands(2);
    decl_statement.location()=symbol.location;
    decl_statement.copy_to_operands(cpp_symbol_expr(symbol));

    // Do we have an initializer that's not code?
    if(symbol.value.is_not_nil() &&
       symbol.value.id()!=ID_code)
    {
      decl_statement.copy_to_operands(symbol.value);
      assert(follow(decl_statement.op1().type())==follow(symbol.type));
    }
    
    new_code.move_to_operands(decl_statement);

    // is there a constructor to be called?
    if(symbol.value.is_not_nil())
    {
      assert(it->find("init_args").is_nil());
      if(symbol.value.id()==ID_code)
        new_code.copy_to_operands(symbol.value);
    }
    else
    {
      exprt object_expr=cpp_symbol_expr(symbol);

      already_typechecked(object_expr);
      
      exprt constructor_call=
        cpp_constructor(
          symbol.location,
          object_expr,
          declarator.init_args().operands());

      if(constructor_call.is_not_nil())
        new_code.move_to_operands(constructor_call);
    }
  }

  code.swap(new_code);
}

/*******************************************************************\

Function: cpp_typecheck_codet::typecheck_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_block(codet &code)
{
  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_scopes.new_block_scope();

  c_typecheck_baset::typecheck_block(code);
}

/*******************************************************************\

Function: cpp_typecheckt::typecheck_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_assign(codet &code)
{

  if(code.operands().size()!=2)
    throw "assignment statement expected to have two operands";

  // turn into a sideeffect
  side_effect_exprt expr(code.get(ID_statement));
  expr.operands() = code.operands();
  typecheck_expr(expr);

  code_expressiont code_expr;
  code_expr.expression()=expr;
  code_expr.location() = code.location();

  code.swap(code_expr);
}
