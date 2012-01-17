/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <iostream>

#include <prefix.h>
#include <context.h>
#include <std_expr.h>
#include <config.h>
#include <namespace.h>

#include <ansi-c/expr2c.h>

#include "dump_c.h"

/*******************************************************************\

Function: convert_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string convert_id(const irep_idt &id)
{
  std::string result=id2string(id);
  
  if(has_prefix(result, "c::"))
    result=std::string(result, 3, std::string::npos);
  
  return result;
}

/*******************************************************************\

Function: indent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct indent
{
  inline explicit indent(unsigned _n):n(_n)
  {
  }

  unsigned n;
};

std::ostream &operator << (std::ostream &out, const indent &indent)
{
  for(unsigned i=0; i<indent.n; i++)
    out << ' ' << ' ';
  return out;
}

#include <sstream>
#if 0
#include <map>
#include <ostream>
#include <cctype>

#include <arith_tools.h>
#include <expr.h>
#include <prefix.h>
#endif
#include <i2string.h>

class goto2cppt
{
public:
  goto2cppt(
    const goto_functionst &_goto_functions,
    const namespacet &_ns):
    goto_functions(_goto_functions),
    ns(_ns)
  {
  }

  void operator()(std::ostream &out);

protected:
  std::string type_to_string(const typet &);
  std::string expr_to_string(const exprt &);

  std::string implicit_declarations(const exprt &expr);
  
  std::string nondet_suffix(const typet &type);

  void convert_compound_declarations(
    std::ostream &os_decl,
    std::ostream &os_body);

  bool supress(const irep_idt &identifier);
 
  void convert_global_variables(std::ostream &os);

  void convert_function_declarations(
    std::ostream &os_decl,
    std::ostream &os_body);

  void convert_instructions(
    const goto_programt &goto_program,
    std::ostream &os);

  void convert_compound_rec(
    const typet &struct_type,
    std::ostream &os);

  const goto_functionst &goto_functions;
  const namespacet &ns;

  irep_idt unique_name(const irep_idt name);

  irep_idt get_global_constant(irep_idt cst, irep_idt type_id)
  {
    irep_idt key = id2string(type_id)+"("+id2string(cst)+")";

    std::map<irep_idt, irep_idt>::const_iterator
      it_find=global_constants.find(key);

    if(it_find != global_constants.end())
      return it_find->second;

    irep_idt new_cst_id = unique_name( "__SCOOT_constant");

    global_constants[key] = new_cst_id;
    global_constant_stream << "const " <<
        id2string(type_id) <<" "<< new_cst_id
        <<"(\"" << id2string(cst) << "\");" << std::endl;

    return new_cst_id;
  }

  std::map<typet, irep_idt> typedef_map;
  std::map<irep_idt, irep_idt> global_constants;
  std::map<irep_idt, irep_idt> global_renaming;
  std::map<irep_idt, irep_idt> local_renaming;

  std::set<std::string> system_headers;
  std::stringstream typedef_stream;          // for types
  std::stringstream global_constant_stream;  // for numerical constants

  std::set<irep_idt> converted;
};

inline std::ostream &operator << (std::ostream &out, goto2cppt &src)
{
  src(out);
  return out;
}

/*******************************************************************\

Function: goto2cppt::operator()

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::operator()(std::ostream &os)
{
  std::stringstream compound_body_stream;
  std::stringstream global_var_stream;
  std::stringstream func_body_stream;

  convert_compound_declarations(os, compound_body_stream);

  convert_global_variables(global_var_stream);
  convert_function_declarations(os, func_body_stream);

  for(std::set<std::string>::const_iterator
      it=system_headers.begin();
      it!=system_headers.end();
      ++it)
    os << "#include <" << *it << ">" << std::endl;

  os << typedef_stream.str();
  os << std::endl;
  typedef_stream.clear();

  os << compound_body_stream.str();
  compound_body_stream.clear();

  os << global_constant_stream.str();
  global_constant_stream.clear();

  os << global_var_stream.str();
  global_var_stream.clear();

  os << func_body_stream.str();
  func_body_stream.clear();

  if(config.main!="c::main" && config.main!="")
    os << "int main(int argc, const char *argv[])" << std::endl
       << "{" << std::endl
       << indent(1) << config.main << "();" << std::endl
       << indent(1) << "return 0;" << std::endl
       << "}" << std::endl;
}

/*******************************************************************\

Function: goto2cppt::convert_compound_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_compound_declarations(
  std::ostream &os_decl,
  std::ostream &os_body)
{
  // declare compound types
  forall_symbols(it, ns.get_context().symbols)
  {
    const symbolt &symbol = it->second;

    if(!symbol.is_type ||
        (symbol.type.id()!=ID_struct &&
         symbol.type.id()!=ID_union &&
         symbol.type.id()!=ID_class))
      continue;

    irep_idt name=unique_name(symbol.base_name);
    global_renaming[symbol.name]=name;

    os_decl << "// " << id2string(symbol.name) << std::endl;
    os_decl << "// " << symbol.location.as_string() << std::endl;
    os_decl << "struct " << name << ";\n" << std::endl;

    // do compound type body
    convert_compound_rec(symbol.type,os_body);
  }

  os_decl << std::endl << std::endl;
}

/*******************************************************************\

Function: goto2cppt::convert_compound_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_compound_rec(
  const typet &type,
  std::ostream &os)
{
  typet final_type = ns.follow(type);

  if(final_type.id() == ID_array)
  {
    convert_compound_rec(final_type.subtype(), os);
    return;
  }
  else if(final_type.id() != ID_struct &&
          final_type.id() != ID_union &&
          final_type.id() != ID_class)
    return;

  struct_union_typet struct_type=to_struct_union_type(final_type);
  irep_idt name=global_renaming[struct_type.get(ID_name)];
  assert(!name.empty());

  if(!converted.insert(name).second)
    return;

  const irept& bases = struct_type.find(ID_bases);
  std::string base_decls;
  forall_irep(parent_it, bases.get_sub())
  {
    assert(parent_it->id() == "base");
    assert(parent_it->get(ID_type) == ID_symbol);

    const irep_idt &base_id=
      parent_it->find(ID_type).get(ID_identifier);
    const irep_idt &renamed_base_id=global_renaming[base_id];
    const symbolt &parsymb=ns.lookup(renamed_base_id);

    convert_compound_rec(parsymb.type,os);

    base_decls += renamed_base_id.as_string() +
      (parent_it+1==bases.get_sub().end()?"":", ");
  }

  /*
  // for the constructor
  string constructor_args;
  string constructor_body;

  std::string component_name =  renaming[compo.get(ID_name)].as_string();
  assert(component_name != "");

  if(it != struct_type.components().begin()) constructor_args += ", ";

  if(compo.type().id() == ID_pointer)
  constructor_args += type_to_string(compo.type()) + component_name;
  else
  constructor_args += "const " + type_to_string(compo.type()) + "& " + component_name;

  constructor_body += indent + indent + "this->"+component_name + " = " + component_name + ";\n";
  */

  std::stringstream struct_body;

  for(struct_union_typet::componentst::const_iterator
      it=struct_type.components().begin();
      it!=struct_type.components().end();
      it++)
  {
    const struct_typet::componentt& compo = *it;

    if(compo.type().id() == ID_code ||
        compo.get_bool("from_base"))
      continue;

    convert_compound_rec(compo.type(), os);

    irep_idt renamed_compo_id = unique_name(compo.get(ID_base_name));
    global_renaming[compo.get(ID_name)] = renamed_compo_id;

    struct_body << indent(1) << "// " << compo.get(ID_name) << std::endl;

    if(compo.type().id() == ID_pointer && 
       compo.type().subtype().id() == ID_code)
    {
      const code_typet &code_type=to_code_type(compo.type().subtype());

      struct_body << indent(1)
                  << type_to_string(code_type.return_type())
                  << " ( * " << renamed_compo_id << ") (";

      for(code_typet::argumentst::const_iterator
          it=code_type.arguments().begin();
          it!=code_type.arguments().end();
          ++it)
        struct_body << type_to_string(it->type()) <<
          (it+1==code_type.arguments().end()?"":", ");

      struct_body << ");" << std::endl;
    }
    else
    {
      struct_body << indent(1) << type_to_string(compo.type())
                  << " " << renamed_compo_id <<  ";" << std::endl;
    }
  }

  os << "struct " << name ;
  if(!base_decls.empty())
    os << ": " << base_decls;
  os << std::endl;
  os << "{" << std::endl;
  os << struct_body.str();

  /*
  if(!struct_type.components().empty())
  {
    os << indent << name << "(){}\n";
    os << indent << "explicit " << name
       << "(" + constructor_args + ")\n";
    os << indent << "{\n";
    os << constructor_body;
    os << indent << "}\n";
  }
  */

  os << "};" << std::endl;
  os << std::endl;
}

/*******************************************************************\

Function: goto2cppt::supress

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool goto2cppt::supress(const irep_idt &identifier)
{
  // we supress some
  if(has_prefix(id2string(identifier), "c::__CPROVER_") ||
     identifier=="c::__func__" ||
     identifier=="c::__FUNCTION__" ||
     identifier=="c::__PRETTY_FUNCTION__")
    return true;
    
  return false;
}

/*******************************************************************\

Function: goto2cppt::convert_global_variables

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_global_variables(std::ostream &os)
{
  forall_symbols(it, ns.get_context().symbols)
  {
    const symbolt &symbol=it->second;
    
    if(!symbol.static_lifetime)
      continue;
      
    irep_idt renamed_id=unique_name(symbol.base_name);
    global_renaming[symbol.name]=renamed_id;

    // we supress some declarations
    if(supress(symbol.name))
      continue;

    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location.as_string() << std::endl;

    os << type_to_string(symbol.type) << " "
       << renamed_id << ";" << std::endl;
    os << std::endl;
  }
}

/*******************************************************************\

Function: goto2cppt::convert_function_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_function_declarations(
  std::ostream &os_decl,
  std::ostream &os_body)
{
  // declare all functions
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
  {
    const symbolt &symb=ns.lookup(it->first);

    const goto_functionst::goto_functiont &goto_function=it->second;

    if(!goto_function.body_available)
      continue;

    irep_idt renamed_function_id=unique_name(symb.base_name);
    global_renaming[symb.name]=renamed_function_id;
   
    if(it->first=="main")
      continue;
  
    const code_typet &code_type=to_code_type(symb.type);
    os_decl << "// " << symb.name << std::endl;
    os_decl << "// " << symb.location.as_string() << std::endl;

    //symb.type.get_bool(ID_C_inlined);
    //os_decl << "inline ";
    os_decl << type_to_string(code_type.return_type()) << " "
            << renamed_function_id;

    os_decl << "(";
    
    if(code_type.arguments().empty())
      os_decl << "void";
    else
    {
      for(unsigned i=0; i<code_type.arguments().size(); i++)
      {
        if(i!=0) os_decl << ", ";
        os_decl << type_to_string(code_type.arguments()[i].type());
      }
    }
    
    os_decl << ");" << std::endl << std::endl;
  }

  // do function bodies
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
  {
    // reset local renaming
    local_renaming.clear();

    const goto_functionst::goto_functiont &goto_function=it->second;

    const symbolt &symb=ns.lookup(it->first);

    if(!goto_function.body_available)
      continue;

    std::map<irep_idt,irep_idt>::const_iterator renaming_it=
      global_renaming.find(symb.name);

    assert(renaming_it!=global_renaming.end());

    irep_idt renamed_function_id=renaming_it->second;
    const code_typet &code_type=to_code_type(symb.type);

    os_body << "// " << symb.name << std::endl;
    os_body << "// " << symb.location.as_string() << std::endl;

    if(symb.name=="main")
    {
      os_body << "int main";
    }
    else
    {
      os_body << type_to_string(code_type.return_type())
              << " " << renamed_function_id;
    }

    os_body << "(";
    
    if(code_type.arguments().empty())
      os_body << "void";
    else
    {
      for(unsigned i=0; i<code_type.arguments().size(); i++)
      {
        if(i!=0) os_body << ", ";
      
        const exprt &arg=code_type.arguments()[i];
        const symbolt &arg_symb=ns.lookup(arg.get(ID_C_identifier));
        irep_idt renamed_arg_id=unique_name(arg_symb.base_name);
        local_renaming[arg_symb.name] = renamed_arg_id;

        if(arg.type().id()==ID_pointer &&
           arg.type().subtype().id()==ID_code)
        {
          const code_typet &code_type=to_code_type(arg.type());
          std::string ret=type_to_string(code_type.return_type())+
                          "( "+id2string(renamed_arg_id) + " *)(";
          for(unsigned i=0; i<code_type.arguments().size(); i++)
          {
            if(i!=0) ret+=", ";
            ret += type_to_string(code_type.arguments()[i].type());
          }
          ret += ")";
        }
        else
        {
          os_body << type_to_string(code_type.arguments()[i].type())
                  << " " << renamed_arg_id;
        }
      }
    }
    
    os_body << ")" << std::endl;

    os_body << "{" << std::endl;
    convert_instructions(goto_function.body, os_body);
    os_body << "}" << std::endl << std::endl;
  }
}

/*******************************************************************\

Function: goto2cppt::convert_instructions

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_instructions(
  const goto_programt &goto_program,
  std::ostream &os)
{
  std::stringstream decl_stream; // for local declarations
  std::stringstream inst_stream; // for instructions
  unsigned thread_vars=0;

  forall_goto_program_instructions(target, goto_program)
  {
    #ifdef DEBUG
    goto_program.output_instruction(ns, "", std::cout, target);
    #endif

    std::string location_string=target->location.as_string();

    if(target->location.get_line()!="" &&
       target->location.get_file()!="" )
    {
      inst_stream << indent(1) 
                  << "// " << target->location.as_string() << std::endl;
      //inst_stream << "#line " 
      //  << target->location.get_line().as_string() << " \"" << target->location.get_file().as_string() << "\"\n";
    }

    if(target->is_target())
      inst_stream << "L" << target->target_number << ":" << std::endl;

    decl_stream << implicit_declarations(target->code);

    switch(target->type)
    {
    case GOTO:
      inst_stream << indent(1);

      if(!target->guard.is_true())
        inst_stream << "if( " << expr_to_string(target->guard) << " ) ";

      inst_stream << "goto ";
      assert(target->targets.size() == 1);
      inst_stream <<"L" << (*target->targets.begin())->target_number <<";" << std::endl;
      break;

    case RETURN:
      inst_stream << indent(1) << "return ";
      if(target->code.operands().size() == 1)
        inst_stream << expr_to_string(target->code.op0());
      inst_stream << ";" << std::endl;
      break;

    case ASSIGN:
      {
        if(target->code.op0().id() == "dynamic_size" ||
           target->code.op0().id() == "valid_object")
        {
          // shall we do something else?
          break;
        }
        else if(target->code.op0().id()==ID_index)
        {
          const index_exprt &index_expr=to_index_expr(target->code.op0());
          if(index_expr.array().id()==ID_symbol)
            if(supress(index_expr.array().get(ID_identifier)))
              continue;
        }
        else if(target->code.op0().id()==ID_symbol)
        {
          if(supress(target->code.op0().get(ID_identifier)))
            continue;
        }

        const codet &assign = target->code;
        const exprt &lhs = assign.op0();
        const exprt &rhs = assign.op1();

        //  assignment of the form `a =  (mask & a) |  ((typecast)b) << right' ?
        if(lhs.type().id() == ID_unsignedbv &&
           rhs.id() == ID_bitor &&
           rhs.operands().size() == 2 &&
           rhs.op0().id() == ID_bitand &&
           rhs.op0().operands().size() == 2 &&
           rhs.op1().id() == ID_shl &&
           rhs.op1().operands().size() == 2)
        {
          const exprt& mask = rhs.op0().op0();
          const exprt& a = rhs.op0().op1();
          exprt b = rhs.op1().op0();
          const exprt& right = rhs.op1().op1();

          if(mask.id() == ID_constant && a == lhs && right.id() == ID_constant)
          {
            const std::string& mask_value = mask.get(ID_value).as_string();
            
            unsigned l = 0;
            for(; l <  mask_value.size() ; l++)
              if(mask_value[l] == '0')
                break;

            unsigned r = l;
            for(; r <  mask_value.size() ; r++)
              if(mask_value[r] == '1')
                break;


            unsigned trail = r;
            for(; trail <  mask_value.size();trail++)
              if(mask_value[trail] == '0')
                break;

            // because of endidaness...
            l = mask_value.size() - 1 - l;
            r = mask_value.size() - r;

            if(trail == mask_value.size())
            {
              unsigned shl = atoi(right.get(ID_C_cformat).c_str());

              if(r == shl)
              {
                  unsigned width = l-r+1;

                  if(width == 1 &&
                     b.id() == ID_typecast &&
                     b.op0().type().id() == ID_bool)
                  {
                    inst_stream << indent(1) << expr_to_string(a) <<
                      ".set_bit(" << shl <<"," <<
                      expr_to_string(b.op0()) << ");\n" ;
                    break;
                  }
                  
                  typet new_type(ID_unsignedbv);
                  new_type.set(ID_width, width);

                  if(b.type() != new_type)
                  {
                    if(b.id() == ID_typecast)
                      b.type() = new_type;
                    else
                      b.make_typecast(new_type);
                  }
               
                  inst_stream << indent(1) <<
                    expr_to_string(a) <<
                      ".set_range<" << width  <<  ", " << r <<
                      ">( " <<  expr_to_string(b) << ");\n" ;
                  break;
              }
            }
          }
        }
        
        if(lhs.type().id() == ID_array && rhs.id() == ID_array)
        {
          // array initialization: x = { a, b, c , ... )
          const array_typet& array_type = to_array_type(lhs.type());
          mp_integer width = string2integer(array_type.size().get(ID_value).as_string(),2);

          unsigned size = integer2long(width);

          index_exprt index_expr;
          index_expr.type() = array_type.subtype();
          index_expr.array() = lhs;
          index_expr.index() = array_type.size();

          const exprt::operandst&  cst = rhs.operands();
          assert(cst.size() == size);

          for(unsigned i = 0; i < size; ++i)
          {
            index_expr.index().set(ID_value, integer2string(i,2));

            inst_stream << indent(1);
            inst_stream << expr_to_string(index_expr) << "="
                        << expr_to_string(cst.at(i)) << ";" << std::endl;
          }
          break;
        }

        inst_stream << indent(1);
        inst_stream << expr_to_string(target->code.op0()) << "="
                    << expr_to_string(target->code.op1()) << ";" << std::endl;
        break;
      }
      
    case FUNCTION_CALL:
      {
        inst_stream << indent(1);

        const code_function_callt &code_func=
          to_code_function_call(to_code(target->code));

        if(code_func.function().id()==ID_symbol)
        {
          irep_idt original_id=to_symbol_expr(code_func.function()).get_identifier();

          if(global_renaming.find(original_id)==global_renaming.end())
          {
            inst_stream << "// ignoring call to `" << original_id <<"'" << std::endl;
            break;
          }

          irep_idt renamed_func_id=global_renaming[original_id];
          assert(renamed_func_id != "");
          if(code_func.lhs().is_not_nil())
            inst_stream << expr_to_string(code_func.lhs()) << " = ";
          inst_stream <<  renamed_func_id << "(";
        }
        else
        {
          assert(code_func.function().id() == ID_dereference);
          if(code_func.lhs().is_not_nil())
            inst_stream << expr_to_string(code_func.lhs()) << " = ";
          inst_stream <<  "( " <<  expr_to_string(code_func.function()) << " )(";
        }

        for(unsigned i=0; i<code_func.arguments().size(); i++)
        {
          if(i!=0) inst_stream << ", ";
          inst_stream << expr_to_string(code_func.arguments()[i]);
        }

        inst_stream <<");" << std::endl;
        break;
      }
      
    case SKIP:
      if(target->is_target())
        inst_stream << indent(1) << "; // SKIP" << std::endl;
      break;

    case LOCATION:
      if(target->is_target())
        inst_stream << indent(1) << "; // LOCATION" << std::endl;
      break;

    case ASSERT:
      system_headers.insert("assert.h");
      inst_stream
        << indent(1) 
        << "assert(" << expr_to_string(target->guard) << ");"
        << std::endl;
      break;

    case ASSUME:
      inst_stream
        << indent(1) 
        << "__CPROVER_assume(" << expr_to_string(target->guard) << ");"
        << std::endl;
      break;

    case END_FUNCTION:
      if(target->is_target())
        inst_stream << indent(1) << "; // END_FUNCTION" << std::endl;
      break;

    case OTHER:
      {
        const codet &code=to_code(target->code);

        if(code.get_statement() == ID_expression)
        {
          // expression has no sideeffect
          if(target->is_target())
            inst_stream << indent(1) << "; // OTHER/expression\n";
        }
        else if(has_prefix(id2string(code.get_statement()), "assign"))
        {
          if(code.op0().id() == "dynamic_size" ||
             code.op0().id() == "valid_object")
          {
            // shall we do something else?
            break;
          }

          inst_stream << indent(1);

          std::string statement = id2string(code.get_statement());
          std::string op_str = statement.substr(std::string("assign").size(), statement.size());

          inst_stream << expr_to_string(target->code.op0()) << " " << op_str << "="
                      << expr_to_string(target->code.op1()) << ";" << std::endl;
          break;
        }
        else if(code.get_statement() == ID_nondet)
        {
          //ps_irep("code",target->code);
          // todo: random input
          throw "Goto2cpp: 'nondet' is not yet implemented\n";
        }
        else if(code.get_statement() == ID_user_specified_predicate)
        {
          //ps_irep("code",target->code);
          // todo: random input
          throw "Goto2cpp: 'user_specified_predicate' is not yet implemented\n";
        }
        else
        {
          std::cerr << target->code.pretty() << std::endl;
          //ps_irep("code",target->code);
          throw "Goto2cpp: instruction not yet supported\n";
        }
        break;
      }

    case DECL:
      /* Ignore; implicit_decls finds it */
      if(target->is_target())
        inst_stream << indent(1) << "; // DECL\n";
      break;
      
    case START_THREAD:
      // we only do one target now
      assert(target->targets.size()==1);
      inst_stream << indent(1) << "// START_THREAD\n";

      {
        // try to use pthreads
        goto_programt::const_targett next=target, next2=target;
        ++next;
        ++next2; ++next2;
        if(next!=goto_program.instructions.end() &&
            next->is_function_call() &&
            to_code_function_call(to_code(next->code)).arguments().size()==1 &&
            next2!=goto_program.instructions.end() &&
            next2->is_end_thread())
        {
          // skip the function call and END_THREAD
          target=next2;
          // copied from FUNCTION_CALL case above
          const code_function_callt &code_func=
            to_code_function_call(to_code(next->code));
          assert(code_func.function().id()==ID_symbol);
          assert(code_func.lhs().is_nil());
          assert(code_func.arguments().size()==1);

          irep_idt original_id=to_symbol_expr(code_func.function()).get_identifier();

          if(global_renaming.find(original_id)==global_renaming.end())
          {
            inst_stream << "// ignoring call to `" << original_id <<"'" << std::endl;
            break;
          }

          irep_idt renamed_func_id=global_renaming[original_id];
          assert(renamed_func_id != "");

          system_headers.insert("pthread.h");
          decl_stream << indent(1)
                      << "pthread_t __pt"
                      << thread_vars++
                      << ";" << std::endl;
          inst_stream << indent(1)
                      << "pthread_create(&__pt"
                      << (thread_vars-1) << ", 0, "
                      << renamed_func_id << ", "
                      << expr_to_string(code_func.arguments()[0])
                      << ");" << std::endl;
        }
        else
          inst_stream << "__CPROVER_ASYNC_"
                      << target->location_number << ":\n"
                      << indent(1) << "goto L"
                      << (*target->targets.begin())->target_number
                      << ";" << std::endl;
      }
      break;

    case END_THREAD:
      inst_stream << indent(1) << "// END_THREAD\n";
      inst_stream << indent(1) << "assume(0);\n";
      break;

    case ATOMIC_BEGIN:
      inst_stream << indent(1) << "// ATOMIC_BEGIN\n";
      inst_stream << indent(1) << "__CPROVER_atomic_begin();\n";
      break;

    case ATOMIC_END:
      inst_stream << indent(1) << "// ATOMIC_END\n";
      inst_stream << indent(1) << "__CPROVER_atomic_end();\n";
      break;

    case DEAD:
    case THROW:
    case CATCH:
    case NO_INSTRUCTION_TYPE:
      std::cerr << target->type << std::endl;
      //ps_irep("code",target->code);
      assert(0);
    }
  }

  os << decl_stream.str();
  os << inst_stream.str();
}

/*******************************************************************\

Function: goto2cppt::type_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string goto2cppt::type_to_string(const typet &type)
{
  std::string ret;

  if(type.id() == ID_bool)
    #if 0
    ret="bool";
    #else
    ret="_Bool";
    #endif
  else if(type.id() == ID_signedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();

    if(width==config.ansi_c.int_width)
      return "int";
    else if(width==config.ansi_c.char_width)
      return "signed char";
    else if(width==config.ansi_c.short_int_width)
      return "short int";
    else if(width==config.ansi_c.long_int_width)
      return "long int";
    else if(width==config.ansi_c.long_long_int_width)
      return "long long int";
    else
      return "__signedbv<"+i2string(width)+">";
  }
  else if(type.id()==ID_unsignedbv)
  {
    unsigned width=to_unsignedbv_type(type).get_width();

    if(width==config.ansi_c.int_width)
      return "unsigned int";
    else if(width==config.ansi_c.char_width)
      return "unsigned char";
    else if(width==config.ansi_c.short_int_width)
      return "unsigned short int";
    else if(width==config.ansi_c.long_int_width)
      return "unsigned long int";
    else if(width==config.ansi_c.long_long_int_width)
      return "unsigned long long int";
    else
      return "__unsignedbv<"+i2string(width)+">";
  }
  else if(type.id()==ID_fixedbv)
  {
    return "double";
  }
  else if(type.id()==ID_floatbv)
  {
    return "double";
  }
  else if(type.id()==ID_pointer)
  {
    const typet &sub=ns.follow(type.subtype());
  
    if(sub.id()==ID_code)
    {
      const code_typet &code_type=to_code_type(sub);

      irep_idt typedef_name=unique_name("typedef_func_ptr");

      typedef_stream << "typedef "
                     << type_to_string(code_type.return_type())
                     << "(* "
                     << typedef_name
                     << ")(";

      if(code_type.arguments().empty())
        typedef_stream << "void";
      else
        for(unsigned i = 0; i<code_type.arguments().size(); i++)
        {
          if(i!=0) typedef_stream << ", ";
          typedef_stream << type_to_string(code_type.arguments()[i].type());
        }

      typedef_stream << ");" << std::endl;
      typedef_map[type]=typedef_name;
      ret=typedef_name.as_string();
    }
    else
    {
      ret+=type_to_string(sub);
      /*if(type.get_bool("#constant"))
        ret += "const ";*/
      ret+=" *";
    }
  }
  else if(type.id()==ID_symbol)
  {
    const irep_idt identifier=to_symbol_type(type).get_identifier();
  
    std::map<irep_idt, irep_idt>::const_iterator it_ren =
      global_renaming.find(identifier);

    if(it_ren==global_renaming.end())
    {
      const symbolt &symb=ns.lookup(identifier);
      assert(symb.is_type);
      ret=type_to_string(symb.type);
    }
    else
      ret=id2string(it_ren->second);
  }
  else if(type.id()==ID_verilogbv)
  {
    return "__verilogbv<"+id2string(type.get(ID_width))+"> ";
  }
  else if(type.id()==ID_c_enum)
  {
    ret="int";
  }
  else if(type.id()==ID_empty)
  {
    ret="void";
  }
  else if(type.id()==ID_constructor ||
          type.id()==ID_destructor)
  {
    ret="void";
  }
  else if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);

    return "__array<"+type_to_string(type.subtype())+", "+expr_to_string(array_type.size())+">";
  }
  else if(type.id()==ID_struct)
  {
    std::map<irep_idt,irep_idt>::const_iterator it_ren =
      global_renaming.find(type.get(ID_name));
    assert(it_ren!=global_renaming.end());
    ret=id2string(it_ren->second);
  }
  else
  {
    std::cerr << id2string(type.id()) << std::endl;
    //ps_irep("type",type);
    assert(0);
  }

  assert(ret != "");

  /*if(type.id() != "pointer" &&
     type.get_bool("#constant"))
    ret = "const " + ret;*/

  return ret;
}

/*******************************************************************\

Function: goto2cppt::nondet_suffix

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string goto2cppt::nondet_suffix(const typet &type)
{
  std::string ret;

  if(type.id() == ID_bool)
    ret="bool";
  else if(type.id()==ID_signedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();

    if(width==config.ansi_c.int_width)
      return "int";
    else if(width==config.ansi_c.char_width)
      return "signed_char";
    else if(width==config.ansi_c.short_int_width)
      return "short_int";
    else if(width==config.ansi_c.long_int_width)
      return "long_int";
    else if(width==config.ansi_c.long_long_int_width)
      return "long_long_int";
    else
      return "signedbv_"+i2string(width);
  }
  else if(type.id()==ID_unsignedbv)
  {
    unsigned width=to_unsignedbv_type(type).get_width();

    if(width==config.ansi_c.int_width)
      return "unsigned_int";
    else if(width==config.ansi_c.char_width)
      return "unsigned_char";
    else if(width==config.ansi_c.short_int_width)
      return "unsigned_short_int";
    else if(width==config.ansi_c.long_int_width)
      return "unsigned_long_int";
    else if(width==config.ansi_c.long_long_int_width)
      return "unsigned_long_long_int";
    else
      return "unsignedbv_"+i2string(width);
  }
  else if(type.id()==ID_fixedbv)
  {
    return "double";
  }
  else if(type.id()==ID_floatbv)
  {
    return "double";
  }
  else if(type.id()==ID_pointer)
  {
    return "ptr";
  }
  else if(type.id()==ID_symbol)
  {
    const irep_idt identifier=to_symbol_type(type).get_identifier();
  
    std::map<irep_idt, irep_idt>::const_iterator it_ren =
      global_renaming.find(identifier);

    if(it_ren==global_renaming.end())
    {
      const symbolt &symb=ns.lookup(identifier);
      assert(symb.is_type);
      ret=nondet_suffix(symb.type);
    }
    else
      ret=id2string(it_ren->second);
  }
  else if(type.id()==ID_c_enum)
  {
    ret="int";
  }
  else if(type.id()==ID_struct)
  {
    std::map<irep_idt,irep_idt>::const_iterator it_ren =
      global_renaming.find(type.get(ID_name));
    assert(it_ren!=global_renaming.end());
    ret=id2string(it_ren->second);
  }
  else
  {
    std::cerr << "nondet of type " << type.id() << std::endl;
    //ps_irep("type",type);
    assert(0);
  }

  assert(ret != "");

  return ret;
}

/*******************************************************************\

Function: goto2cppt::expr_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string goto2cppt::expr_to_string(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt identifier=to_symbol_expr(expr).get_identifier();
  
    std::map<irep_idt, irep_idt>::const_iterator it_loc =
      local_renaming.find(identifier);

    if(it_loc!=local_renaming.end())
      return id2string(it_loc->second);

    std::map<irep_idt, irep_idt>::const_iterator it_glob=
      global_renaming.find(identifier);

    if(it_glob!=global_renaming.end())
      return id2string(it_glob->second);
  }
  else if(expr.id()==ID_member)
  {
    irep_idt renamed_id=global_renaming[expr.get(ID_component_name)];
    assert(renamed_id!="");
    return expr_to_string(expr.op0())+"."+id2string(renamed_id);
  }
  else if(expr.id()==ID_dereference)
  {
    return "(*"+expr_to_string(expr.op0())+")";
  }
  else if(expr.id()==ID_plus ||
          expr.id()==ID_minus ||
          expr.id()==ID_mult)
  {
    assert(expr.operands().size()>=2);

    std::string str;

    if(expr.op0().type().id() == ID_pointer ||
       expr.op1().type().id() == ID_pointer ||
       expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      str="("+expr_to_string(expr.operands()[0])+
              expr.id().as_string()+
              expr_to_string(expr.operands()[1])+")";
    }
    else
      str=expr_to_string(expr.operands()[0])+
          expr.id().as_string()+"="+
          expr_to_string(expr.operands()[1]);

    for(unsigned i = 2; i < expr.operands().size(); i++ )
    {
       const exprt& opleft = expr.operands()[i-1];
       const exprt& opright = expr.operands()[i];

       if( opleft.type().id() == ID_pointer ||
           opright.type().id() == ID_pointer)
        str += expr.id().as_string() + expr_to_string(expr.operands()[i]);
       else
        str += expr.id().as_string() +"=" + expr_to_string(expr.operands()[i]);
    }

    str = "(" + str + ")";
    return str;
  }
  else if(expr.id()==ID_div ||
          expr.id()==ID_lt  || expr.id()==ID_gt ||
          expr.id()==ID_le  || expr.id()==ID_ge)
  {
    assert(expr.operands().size() == 2);
    return "("+expr_to_string(expr.op0())+id2string(expr.id())
              +expr_to_string(expr.op1())+")";
  }
  else if(expr.id()==ID_mod)
  {
    assert(expr.operands().size() == 2);
    return "("+expr_to_string(expr.op0())+"%"
              +expr_to_string(expr.op1())+")";
  }
  else if(expr.id()==ID_equal)
  {
    assert(expr.operands().size() == 2);
    return "("+expr_to_string(expr.op0())+"=="
              +expr_to_string(expr.op1())+")";
  }
  else if(expr.id()==ID_notequal)
  {
    assert(expr.operands().size() == 2);
    return "("+expr_to_string(expr.op0())+"!="
              +expr_to_string(expr.op1())+")";
  }
  else if(expr.id()==ID_and)
  {
    assert(expr.operands().size() >= 2);
    std::string str="(";
    str+=expr_to_string(expr.operands()[0]);
    for(unsigned i=1; i<expr.operands().size(); i++)
      str+=" && "+expr_to_string(expr.operands()[i]);
    str+=")";
    return str;
  }
  else if(expr.id() == ID_or)
  {
    assert(expr.operands().size() >= 1);
    std::string str="(";
    str+=expr_to_string(expr.operands()[0]);
    for(unsigned i = 1; i < expr.operands().size(); i++ )
      str += " || "+expr_to_string(expr.operands()[i]);
    str+=")";
    return str;
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size() == 1);
    return "(!"+expr_to_string(expr.op0())+")";
  }
  else if(expr.id() == ID_bitand)
  {
    assert(expr.operands().size() >= 2);

    std::string str;
    if(expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      str = "("+ expr_to_string(expr.operands()[0]) +
            " & " + expr_to_string(expr.operands()[1]) +")";
    }
    else
      str = expr_to_string(expr.operands()[0])
            + " &= " + expr_to_string(expr.operands()[1]);

    for(unsigned i = 2; i < expr.operands().size(); i++ )
      str += " &= " + expr_to_string(expr.operands()[i]);

    str="("+str+")";

    return str;
  }
  else if(expr.id()==ID_bitor)
  {
    assert(expr.operands().size() >= 2);

    std::string str;

    if(expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      str = "("+ expr_to_string(expr.operands()[0]) +
            " | " + expr_to_string(expr.operands()[1]) +")";
    }
    else
      str = expr_to_string(expr.operands()[0])
            + " |= " + expr_to_string(expr.operands()[1]);

    for(unsigned i = 2; i < expr.operands().size(); i++ )
      str += " |= " + expr_to_string(expr.operands()[i]);
    str = "(" + str + ")";
    return str;

  }
  else if(expr.id()==ID_bitxor)
  {
    std::string str;
    
    if(expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      str = "("+ expr_to_string(expr.operands()[0]) +
            " ^ " + expr_to_string(expr.operands()[1]) +")";
    }
    else
      str = expr_to_string(expr.operands()[0])
            + " ^= " + expr_to_string(expr.operands()[1]);
    for(unsigned i = 2; i < expr.operands().size(); i++ )
      str += " ^= " + expr_to_string(expr.operands()[i]);

    str = "(" + str + ")";

    return str;
  }
  else if(expr.id()==ID_bitnot)
  {
    assert(expr.operands().size() == 1);
    return "(~ " + expr_to_string(expr.op0()) + ")";
  }
  else if(expr.id()==ID_shl)
  {
    assert(expr.operands().size() == 2);

    std::string shf_str;
    if(expr.op1().id()==ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv ||
             expr.op1().type().id() == ID_signedbv);

      std::string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)),2);
      shf_str = integer2string(cst, 10);
      assert(shf_str != "");
    }
    else
      shf_str=expr_to_string(expr.op1());

    if(expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      return "(" + expr_to_string(expr.op0()) +" << " + shf_str + " )";
    }
    return "(" + expr_to_string(expr.op0()) +" <<= " + shf_str + " )";
  }
  else if(expr.id() == ID_lshr || expr.id() == ID_ashr)
  {
    assert(expr.operands().size() == 2);

    if(expr.op1().id()==ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv ||
             expr.op1().type().id() == ID_signedbv);

      std::string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)),2);
      std::string str = integer2string(cst, 10);
      assert(str != "");
      return "(" + expr_to_string(expr.op0()) +" >> "+str + " )";
    }

    return "("+expr_to_string(expr.op0())+" >> "+
               expr_to_string(expr.op1())+")";
  }
  else if(expr.id() == ID_unary_minus)
  {
    assert(expr.operands().size() == 1);
    return "(" + type_to_string(expr.op0().type())+"(0) - "+
           expr_to_string(expr.op0()) + " ) ";
  }
  else if(expr.id() == ID_constant)
  {
    if(expr.type().id() == ID_signedbv ||
       expr.type().id() == ID_unsignedbv)
    {
      std::string width_str = id2string(expr.type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);

      mp_integer cst = string2integer(id2string(expr.get(ID_value)),2);
      std::string str = integer2string(cst, 10);
      assert(str != "");
      return str;

      #if 0

      if(width <= config.ansi_c.int_width)
      {
        mp_integer cst = string2integer(id2string(expr.get(ID_value)),2);
        std::string str = integer2string(cst, 10) ;
        assert(str != "");
        return "__" + id2string(expr.type().id()) + "<" + width_str + "> ( " + str +")";
      }
      else
      {
        std::string type_id = "__" + id2string(expr.type().id()) + "<" +width_str + ">";
        return id2string(get_global_constant(id2string(expr.get(ID_value)), type_id));
      }
      #endif
    }

    if(expr.type().id() == ID_bool)
      return expr.get_string(ID_value);

    if(expr.type().id() == ID_pointer)
    {
      assert(expr.get(ID_value)==ID_NULL);
      return "0";
    }

    if(expr.type().id() == ID_verilogbv)
    {
      if(expr.type().get(ID_width) == "1")
      {
        irep_idt value = expr.get(ID_value);
        if(value == "0")
          return "LOGIC_0";
        if(value == "1")
          return "LOGIC_1";
        if(value == "z")
          return "LOGIC_Z";
        if(value == "x")
          return "LOGIC_X";
      }
      else
      {
        std::string width_str = id2string(expr.type().get(ID_width));
        mp_integer width = string2integer(width_str,10);
        assert(width != 0);
        std::string type_id = "__" + id2string(expr.type().id()) + "<" +width_str + ">";
        return  type_id +"("+ id2string(get_global_constant(expr.get("value"), type_id))+")";
      }
    }

    if(expr.type().id()==ID_c_enum)
    {
      std::string str = "__signedbv<" + id2string(expr.type().get(ID_width)) +
        "> (" + id2string(expr.get(ID_value)) + ")";
      return str;
    }

    if(expr.type().id()==ID_symbol)
    {
      typet final_type = ns.follow(expr.type());
      exprt expr2(expr);
      expr2.type() = final_type;
      return expr_to_string(expr2);
    }
  }
  else if(expr.id()==ID_typecast)
  {
    assert(expr.operands().size()==1);
    
    if(expr.type().id()==ID_bool)
    {
      return "("+type_to_string(expr.type())+")("+
             expr_to_string(expr.op0())+")";
    }

    if(expr.type().id() == ID_pointer && 
       expr.op0().type().id() == ID_pointer)
    {
      const typet& subtype = ns.follow(expr.type().subtype());
      const typet& op_subtype = ns.follow(expr.op0().type().subtype());
      if(subtype.id() == ID_struct &&
          op_subtype.id() == ID_struct)
      {
        std::list<irep_idt> wkl;

        wkl.push_back(subtype.get(ID_name));
        std::set<irep_idt> bases;
        while(!wkl.empty())
        {
          irep_idt id = wkl.back();
          wkl.pop_front();
          bases.insert(id);
          const symbolt& symb = ns.lookup(id);
          const struct_typet& struct_type = to_struct_type(symb.type);
          const irept::subt& subs = struct_type.find(ID_bases).get_sub();
          for(unsigned i = 0; i < subs.size(); i++)
            wkl.push_back(subs[i].find(ID_type).get(ID_identifier));
        }

        if(bases.count(op_subtype.get(ID_name)))
        {
          return "static_cast<" + type_to_string(expr.type()) + "> (" +
                 expr_to_string(expr.op0()) + ")";
        }

        bases.clear();
        wkl.clear();
        wkl.push_back(op_subtype.get(ID_name));
        while(!wkl.empty())
        {
          irep_idt id = wkl.back();
          wkl.pop_front();
          bases.insert(id);
          const symbolt& symb = ns.lookup(id);
          const struct_typet& struct_type = to_struct_type(symb.type);
          const irept::subt& subs = struct_type.find(ID_bases).get_sub();
          for(unsigned i = 0; i < subs.size(); i++)
            wkl.push_back(subs[i].find(ID_type).get(ID_identifier));
        }

        //if(bases.count(subtype.get(ID_name)))
        {
          return "static_cast<" + type_to_string(expr.type()) + "> (" +
                 expr_to_string(expr.op0()) + ")";
        }

        std::cerr << "Warning conversion from " << op_subtype.get("name")
                  << " to " << subtype.get(ID_name) << " is not safe!\n";
      }
    }

    return "((" + type_to_string(expr.type()) + ") " +
           expr_to_string(expr.op0()) + ")";
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size() == 1);
    return "(&"+expr_to_string(expr.op0())+")";
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size() == 2);

    if(expr.op1().id()==ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv ||
             expr.op1().type().id() == ID_signedbv);

      std::string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str, 10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)), 2);
      std::string str = integer2string(cst, 10);
      assert(str != "");
      return "(" +expr_to_string(expr.op0()) + "[" + str + " ] )";
    }

    return "(" +expr_to_string(expr.op0())+
           "[" + expr_to_string(expr.op1())+ "])";
  }
  else if(expr.id() == ID_extractbits)
  {
    assert(expr.operands().size()==3);

    return "__" + id2string(expr.type().id())+"<"+ id2string(expr.type().get(ID_width)) + "> ("
           + expr_to_string(expr.op0()) + ", "
           + expr_to_string(expr.op1()) + ", "
           + expr_to_string(expr.op2()) + " )";
  }
  else if(expr.id() == ID_extractbit)
  {
    assert(expr.operands().size()==2);

    if(expr.op1().id() == ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv || expr.op1().type().id() == ID_signedbv);
      std::string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)),2);
      std::string str = integer2string(cst, 10);
      assert(str != "");
      return "((" + expr_to_string(expr.op0()) + ")[ "+ str + " ])";
    }

    return "((" + expr_to_string(expr.op0()) + ")[ "
           + expr_to_string(expr.op1()) + " ])";
  }
  else if(expr.id()==ID_sideeffect)
  {
    const irep_idt &statement=to_sideeffect_expr(expr).get_statement();
  
    if(statement==ID_cpp_new)
    {
      assert(expr.type().id()==ID_pointer);
      return "new "+type_to_string(expr.type().subtype())+"()";
    }
    else if(statement==ID_cpp_new_array)
    {
      assert(expr.type().id()==ID_pointer);
      return "(new " + type_to_string(expr.type().subtype()) +
             "[ " + expr_to_string((const exprt &)expr.find(ID_size)) + "])";
    }
    else if(statement==ID_nondet)
    {
      return "nondet_"+nondet_suffix(expr.type())+"()";
    }
  }
  else if(expr.id() == ID_string_constant)
  {
    std::string get_value = expr.get(ID_value).as_string();
    std::string filtered_value;
    for(unsigned i=0; i < get_value.length(); i++)
    {
      if(get_value[i] == '\n')
        filtered_value += "\\n";
      else if(get_value[i] == '\\')
        filtered_value +="\\\\";
      else if(get_value[i] == '\"')
        filtered_value += "\\\"";
      else
        filtered_value += get_value[i];
      filtered_value += "\\000\\000\\000";  //  convert char to int.
    }
    filtered_value +="\\000\\000\\000";
    return "((__signedbv<8>*)\""+ filtered_value +"\")";
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    return "("+expr_to_string(expr.op0())+
           "? "+expr_to_string(expr.op1())+
           ":"+expr_to_string(expr.op2())+")";
  }
  else if(expr.id() == ID_infinity)
  {
    return "CPROVER_INFINITY";
  }
  else if(expr.id() == ID_concatenation)
  {
    return "__concatenation( "
           + expr_to_string(expr.op0())
           + ", " + expr_to_string(expr.op1())
           + ")";
  }
  else if(expr.id() == ID_with)
  {
    assert(expr.operands().size() == 3);

    if(expr.op0().type().id() == ID_array)
    {
      std::string T = type_to_string(expr.type().subtype());
      std::string W = expr_to_string(
          to_array_type(expr.type()).size());

      std::string src = expr_to_string(expr.op0());
      std::string index = expr_to_string(expr.op1());
      std::string value = expr_to_string(expr.op2());

      std::string ret = "(__array< "+ T + ", " + W  + " >&)";

      if(expr.op0().id() == ID_with)
      {
        // fast version: src[index] = v
        ret += "__with< " + T + ", " + W  + " >" +
               "(" + src + ", " + index + ", " + value + ")";
      }
      else
      {
        // slow version: src is duplicated
        ret += "__const_with< " + T + ", " + W  + ">" +
          "(" + src + ", " + index + ", " + value + ")";
      }
      ret = "(" +ret + ")";
      return ret;
    }
    else
    {
      const typet &t=ns.follow(expr.type());
      assert(t.id() == ID_struct);

      std::string src = expr_to_string(expr.op0());
      std::string value = expr_to_string(expr.op2());

      std::string member =
        global_renaming[expr.get(ID_component_name)].as_string();

      std::string type =
        global_renaming[t.get(ID_name)].as_string();

      return "__with("+ src+ ", &" + type + "::" + member + ", " +
        value + ")";
    }
  }
  else if(expr.id() == ID_array_of)
  {
    assert(expr.operands().size() == 1);
    assert(expr.type().id() == ID_array);
    assert(expr.type().subtype() == expr.op0().type());

    std::string T = type_to_string(expr.type().subtype());
    std::string W = expr_to_string(
      to_array_type(expr.type()).size());
    std::string arg = expr_to_string(expr.op0());
    return "__array<" + T + ", " + W + " >("+ arg + ")";
  }
  else if(expr.id() == ID_struct)
  {
    const struct_typet& struct_type = 
      to_struct_type(ns.follow(expr.type()));
    const struct_typet::componentst& components = struct_type.components();
    const exprt::operandst& operands = expr.operands();

    std::string ret=global_renaming[struct_type.get(ID_name)].as_string()+"(";
    
    assert(operands.size() == components.size());
    if( 0 < operands.size())
    {
      assert(operands[0].type() == components[0].type());
      ret += expr_to_string(operands[0]);
    }

    for(unsigned i = 1; i < operands.size(); i++)
    {
      assert(operands[i].type() == components[i].type());
      ret += ", " +expr_to_string(operands[i]);
    }
    ret += ")";
    return ret;
  }
  else if(expr.id() == ID_pointer_object)
  {
    return "POINTER_OBJECT";
  }

  //ps_irep("expr",expr);
  std::cout << expr << std::endl;
  assert(0);
}

/*******************************************************************\

Function: goto2cppt::unique_name

Inputs:

Outputs:

Purpose:

\*******************************************************************/

irep_idt goto2cppt::unique_name(irep_idt name)
{
   static std::map<irep_idt,int> count;
   std::string str(id2string(name));

   std::string::iterator it = str.begin();
   while(it != str.end())
   {
           if(!std::isalnum(*it) && (*it) != '_')
             it = str.erase(it);
           else it++;
   }

   if(isdigit(*(str.begin())))
       str.insert(str.begin(),'_');

   if(str == "this" || str == "operator" || str == "main")
     str = "_"+ str;

   if(str == "")
     str = "func";

   do
   {
       int c = count[str]++;

       if( c == 0)
           break;

       std::stringstream stream;
       stream << c;
       str += stream.str();
   }
   while(true);

   return str;
}

/*******************************************************************\

Function: goto2cppt::implicit_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string goto2cppt::implicit_declarations(const exprt &expr)
{
  std::string ret;

  if(expr.id()==ID_symbol)
  {
    const irep_idt identifier=to_symbol_expr(expr).get_identifier();
  
    std::map<irep_idt,irep_idt>::const_iterator it_glob =
      global_renaming.find(identifier);
    
    if(it_glob==global_renaming.end())
    {
      std::map<irep_idt, irep_idt>::const_iterator it_loc =
        local_renaming.find(identifier);

      if(it_loc==local_renaming.end())
      {
        const symbolt &symb=ns.lookup(identifier);

        if(symb.type.id()!=ID_code)
        {
          // not yet declared
          irep_idt renamed_id=unique_name(symb.base_name);
          local_renaming[symb.name]=renamed_id;
          ret += "  " + type_to_string(symb.type)
                      + " " + renamed_id.as_string()  + ";\n";
        }
      }
    }
  }
  else
    forall_operands(it, expr)
      ret+=implicit_declarations(*it);

  return ret;
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out)
{
  goto2cppt goto2cpp(src, ns);
  out << goto2cpp;
}

