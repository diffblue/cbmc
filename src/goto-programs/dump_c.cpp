/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <iostream>

#include <prefix.h>
#include <context.h>

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

Function: gen_indent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_indent(unsigned indent, std::ostream &out)
{
  for(unsigned i=0; i<indent; i++) out << ' ' << ' ';
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  unsigned indent,
  const goto_programt &goto_program,
  const goto_programt::const_targett t,
  const namespacet &ns,
  std::ostream &out)
{
  switch(t->type)
  {
  case GOTO:
    break;
  
  case ASSUME:
    break;
  
  case ASSERT:
    break;
  
  case OTHER:
    break;
    
  case DECL:
    break;
  
  case SKIP:
  case LOCATION:
  case END_FUNCTION:
    // ignore
    break;

  case DEAD:
    out << "/* ignoring DEAD */" << std::endl << std::endl;
    break;
  
  case START_THREAD:
    out << "/* ignoring START_THREAD */" << std::endl << std::endl;
    break;
  
  case END_THREAD:
    out << "/* ignoring END_THREAD */" << std::endl << std::endl;
    break;
  
  case ATOMIC_BEGIN:
    out << "/* ignoring ATOMIC_BEGIN */" << std::endl << std::endl;
    break;

  case ATOMIC_END:
    out << "/* ignoring ATOMIC_END */" << std::endl << std::endl;
    break;
  
  case RETURN:
    gen_indent(indent, out);
    out << "return";
    out << ";" << std::endl;
    break;
  
  case ASSIGN:
    break;
  
  case FUNCTION_CALL:
    break;
  
  default:
    throw "unexpected goto instruction";
  }
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  const goto_functionst::function_mapt::const_iterator f_it,
  const namespacet &ns,
  std::ostream &out)
{
  out << "/* " << f_it->first << " */" << std::endl;

  const symbolt &symbol=ns.lookup(f_it->first);
  
  out << "/* " << symbol.location << " */" << std::endl;
  out << std::endl;

  const code_typet &type=to_code_type(ns.follow(symbol.type));
  
  out << type2c(type.return_type(), ns);
  out << " ";
  out << convert_id(symbol.name);
  
  const code_typet::argumentst &arguments=
    type.arguments();

  if(arguments.empty())
  {
    out << "(void)" << std::endl;
  }
  else
  {
    out << "(" << std::endl;
    for(code_typet::argumentst::const_iterator
        a_it=arguments.begin();
        a_it!=arguments.end();
        a_it++)
    {
      if(a_it!=arguments.begin()) out << ", " << std::endl;
      out << "  ";
      out << type2c(a_it->type(), ns);
      out << " " << convert_id(a_it->get_identifier());
    }
    out << ")" << std::endl;
  }
  
  out << "{" << std::endl;
  
  const goto_programt &body=f_it->second.body;

  forall_goto_program_instructions(it, body)
    dump_c(1, body, it, ns, out);

  out << "}  /* end of " << symbol.name << " */" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Module: 

Author: 

\*******************************************************************/

#include <map>
#include <ostream>
#include <sstream>
#include <cctype>

#include <namespace.h>

class goto2cppt
{
public:
  goto2cppt(
    const namespacet& ns,
    const goto_functionst& goto_functions,
    std::ostream& os):
      goto_functions(goto_functions), ns(ns){}

  void convert(std::ostream& os);

protected:

   std::string type_to_string(const typet&, bool keep_int = false);
   std::string expr_to_string(const exprt&,
                              const std::map<irep_idt,irep_idt>&, bool keep_int = false);

   std::string implicit_declarations(const exprt& expr,
                      std::map<irep_idt,irep_idt>& local_renaming);

   void convert_compound_declarations(std::ostream& os_decl,
                                      std::ostream& os_body);
   void convert_global_variables(std::ostream& os);
   void convert_function_declarations(std::ostream& os);


   void convert_instructions(const goto_programt& goto_program,
                             std::map<irep_idt, irep_idt>&, std::ostream& os);

   void convert_compound_rec(const struct_typet& struct_type, std::ostream& os);

   const goto_functionst& goto_functions;

   irep_idt unique_name(irep_idt name);


   irep_idt get_global_constant(irep_idt cst, irep_idt type_id)
   {
       irep_idt key = id2string(type_id)+"("+id2string(cst)+")";

       std::map<irep_idt, irep_idt>::const_iterator it_find
            = global_constants.find(key);

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

   const namespacet& ns;
   std::map<irep_idt,irep_idt> renaming;

   std::stringstream typedef_stream;          // for types
   std::stringstream global_constant_stream;  // for numerical constants
};

#include <arith_tools.h>
#include <config.h>
#include <expr.h>
#include <prefix.h>
#include <std_expr.h>
#include <i2string.h>

using namespace std;

/*******************************************************************\

Function: goto2cppt::convert

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert(std::ostream &os)
{
  os << "// file automatically generated by Scoot -- "
     << __DATE__ << " " << __TIME__ << endl;
  os << endl;
  os << "#ifndef CPROVER_INFINITY "  << endl;
  os << "#define CPROVER_INFINITY 1" << endl;
  os << "#endif" << endl;
  os << endl;
  os << "#include <__bv.h>" << endl;
  os << "#include <__nondet.h>" << endl;
  os << "#include <__print.h>"  << endl;
  os << "#include <__schedule.h>" << endl;
  os << "#include <iostream>" << endl;
  os << std::endl;
  os << "namespace scoot {" << endl;
  os << endl;

  std::stringstream compound_decl_stream;
  std::stringstream compound_body_stream;
  std::stringstream global_var_stream;
  std::stringstream func_decl_stream;

  convert_compound_declarations(compound_decl_stream,
                                compound_body_stream);

  os << compound_decl_stream.str();
  compound_decl_stream.clear();

  convert_global_variables(global_var_stream);
  convert_function_declarations(func_decl_stream);

  os << typedef_stream.str();
  os << std::endl;
  typedef_stream.clear();

  os << compound_body_stream.str();
  compound_body_stream.clear();

  os << global_constant_stream.str();
  global_constant_stream.clear();

  os << global_var_stream.str();
  global_var_stream.clear();

  os << func_decl_stream.str();
  func_decl_stream.clear();
  os << "} // end scoot" << endl;
  os << "int main() {" << endl
     << "  scoot::main();" << endl
     << "  return 0;" << endl
     << "}" << endl;
}

/*******************************************************************\

Function: goto2cppt::convert_compound_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_compound_declarations(std::ostream& os_decl,
                                              std::ostream& os_body)
{
  string struct_decls;
  string struct_bodies;

  std::set<irep_idt> converted;

  // declare compound types
  for(contextt::symbolst::const_iterator it =
      ns.get_context().symbols.begin();
      it != ns.get_context().symbols.end();
      it++)
  {
    const symbolt& symbol = it->second;

    if(!symbol.is_type)
      continue;

    if(symbol.type.id()==ID_struct)
    {
      irep_idt name = unique_name(symbol.base_name);
      renaming[symbol.name] = name;
      os_decl << "// " << id2string(symbol.name) << endl;
      os_decl << "// " << symbol.location.as_string() << endl;
      os_decl << "struct " << name << ";\n" << endl;
    }
  }

  os_decl << endl << endl;

  // do compound type bodies
  for(contextt::symbolst::const_iterator it =
      ns.get_context().symbols.begin();
      it != ns.get_context().symbols.end();
      it++)
  {
    const symbolt& symbol = it->second;

    if(!symbol.is_type)
      continue;

    if(symbol.type.id()==ID_struct)
    {
      const struct_typet& struct_type = to_struct_type(symbol.type);
      convert_compound_rec(struct_type,os_body);
    }
  }

}


/*******************************************************************\

Function: goto2cppt::convert_global_variables

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_global_variables(std::ostream& os)
{
  for(contextt::symbolst::const_iterator it =
      ns.get_context().symbols.begin();
      it != ns.get_context().symbols.end();
      it++)
  {
    const symbolt& symbol = it->second;

    if(!symbol.static_lifetime)
      continue;

    irep_idt renamed_id = unique_name(symbol.base_name);
    renaming[symbol.name] = renamed_id;

    os << "// " << symbol.name << endl;
    os << "// " << symbol.location.as_string() << endl;

    os << type_to_string(symbol.type) << " "
       << renamed_id << ";" << endl;
    os << endl;
  }
}

/*******************************************************************\

Function: goto2cppt::convert_function_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_function_declarations(std::ostream& os)
{
  // declare all functions
  for(goto_functionst::function_mapt::const_iterator it =
      goto_functions.function_map.begin();
      it !=  goto_functions.function_map.end();
      it ++)
  {
    const symbolt& symb = ns.lookup(it->first);

    irep_idt renamed_function_id;


    const goto_functionst::goto_functiont& goto_function = it->second;

    if(!goto_function.body_available)
      continue;

    renamed_function_id =  unique_name(symb.base_name);
    renaming[symb.name] = renamed_function_id;
   
    const code_typet& code_type = to_code_type(symb.type);
    os << "// " << id2string(symb.name) << endl;
    os << "// " << symb.location.as_string() << endl;

    if(symb.name == "main")
      os << "int main ";
    else
    {
      symb.type.get_bool(ID_C_inlined);
      os << "inline ";
      os << type_to_string(code_type.return_type());
      os << id2string(renamed_function_id);
    }

    os << "( ";
    unsigned i = 0;
    for(; i+1 < code_type.arguments().size(); i++)
      os << type_to_string(code_type.arguments()[i].type()) << ", ";
    if(i < code_type.arguments().size())
      os << type_to_string(code_type.arguments()[i].type());
    os << "); ";
    os << endl << endl;
  }

  // do function body
  for(goto_functionst::function_mapt::const_iterator it =
      goto_functions.function_map.begin();
      it !=  goto_functions.function_map.end();
      it ++)
  {
    map<irep_idt,irep_idt> local_renaming;

    const goto_functionst::goto_functiont& goto_function = it->second;

    const symbolt& symb = ns.lookup(it->first);

    if(!goto_function.body_available)
      continue;

    map<irep_idt,irep_idt>::const_iterator renaming_it = renaming.find(symb.name);
    assert(renaming_it != renaming.end());
    irep_idt renamed_function_id = renaming_it->second;
    const code_typet& code_type = to_code_type(symb.type);

    os << "// " << id2string(symb.name) << endl;
    os << "// " << symb.location.as_string() << endl;

    if(symb.name == "main")
    {
      os << "int main";
    }
    else
    {
      os << type_to_string(code_type.return_type());
      os << id2string(renamed_function_id);
    }

    os << "( ";
    unsigned i = 0;
    for(; i+1 < code_type.arguments().size(); i++)
    {
      const exprt& arg =  code_type.arguments()[i];
      const symbolt& arg_symb = ns.lookup(arg.get(ID_C_identifier));
      irep_idt renamed_arg_id = unique_name(arg_symb.base_name);
      local_renaming[arg_symb.name] = renamed_arg_id;

      if(arg.type().id() == ID_array)
      {
        os << type_to_string(arg.type().subtype()) << id2string(renamed_arg_id)
           << " [ " << arg.type().get(ID_size) << " ]";
      }
      else if(arg.type().id() == ID_pointer &&
              arg.type().subtype().id() == ID_code )
      {
        const code_typet& code_type = to_code_type(arg.type());
        string ret = type_to_string(code_type.return_type()) +
                     "( "+id2string(renamed_arg_id) + " *)(";
        unsigned i = 0;
        for(; i+1 < code_type.arguments().size(); i++)
          ret += type_to_string(code_type.arguments()[i].type()) + ", ";
        if(i < code_type.arguments().size())
          ret += type_to_string(code_type.arguments()[i].type());
        ret += ") ";
      }
      else
      {
        os << type_to_string(code_type.arguments()[i].type())
           << renamed_arg_id << ", ";
      }
    }
    if(i < code_type.arguments().size())
    {
      const exprt& arg =  code_type.arguments()[i];
      const symbolt& arg_symb = ns.lookup(arg.get(ID_C_identifier));
      irep_idt renamed_arg_id = unique_name(arg_symb.base_name);
      local_renaming[arg.get(ID_C_identifier)] = renamed_arg_id;
      if(arg.type().id() == ID_array)
      {
        os << type_to_string(arg.type().subtype()) << id2string(renamed_arg_id)
           << " [ " << arg.type().get(ID_size) << " ]";
      }
      else if(arg.type().id() == ID_pointer &&
              arg.type().subtype().id() == ID_code )
      {
        const code_typet& code_type = to_code_type(arg.type());
        string ret = type_to_string(code_type.return_type()) +
                     "( "+id2string(renamed_arg_id) + " *)(";
        unsigned i = 0;
        for(; i+1 < code_type.arguments().size(); i++)
          ret += type_to_string(code_type.arguments()[i].type());
        if(i < code_type.arguments().size())
          ret += type_to_string(code_type.arguments()[i].type());
        ret += ") ";
      }
      else
      {
        os << type_to_string(code_type.arguments()[i].type())<< id2string(renamed_arg_id);
      }
    }
    os << ")" << endl;
    os << "{" << endl;

    if(symb.name == "main")
    {
      os << "    std::cout << \"Scoot -- "
         << __DATE__ << "  " << __TIME__ << "\"<< std::endl;" << endl
         << "    std::cout << \"Author: Nicolas Blanc\" << std::endl << "
         << "std::endl;" << endl;
    }

    convert_instructions(goto_function.body, local_renaming,os);
    os << "}" << endl << endl;
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
  map<irep_idt, irep_idt> &local_renaming,
  std::ostream &os)
{
  std::string indent="  ";
  std::stringstream decl_stream;                  // for local declarations
  std::stringstream inst_stream;                  // for instructions

  forall_goto_program_instructions(target, goto_program)
  {
    #ifdef DEBUG
    goto_program.output_instruction(ns, "", std::cout,target);
    #endif

    std::string location_string = target->location.as_string();
    if(target->location.get_line() != "" &&
       target->location.get_file() != "" )
    {
      inst_stream << indent << "// " << target->location.as_string() << endl;
      //inst_stream << "#line " 
      //  << target->location.get_line().as_string() << " \"" << target->location.get_file().as_string() << "\"\n";
    }

    if(target->is_target())
    {
      inst_stream << indent << "L" << target->target_number << ":" << endl;
      if(target->type == END_FUNCTION) inst_stream << ";" << endl;
    }

    decl_stream << implicit_declarations(target->code, local_renaming);

    switch(target->type)
    {
    case GOTO:
      inst_stream << indent;
      if(!target->guard.is_true())
      {
        inst_stream << "if( " << expr_to_string(target->guard,local_renaming) << " ) ";
      }
      inst_stream << "goto ";
      assert(target->targets.size() == 1);
      inst_stream <<"L" << (*target->targets.begin())->target_number <<";" << endl;
      break;

    case  RETURN:
      inst_stream << indent << "return ";
      if(target->code.operands().size() == 1)
        inst_stream << expr_to_string(target->code.op0(),local_renaming);
      inst_stream << ";" << endl;
      break;

    case ASSIGN:
      {
        if(target->code.op0().id() == "dynamic_size" ||
             target->code.op0().id() == "valid_object")
        {
            // shall we do something else?
            break;
        }
        else if (target->code.op0().id() == ID_index)
        {
          const index_exprt& index_expr = to_index_expr(target->code.op0());
          if(index_expr.array().id() == ID_symbol)
          {
            const symbolt& symb = ns.lookup(index_expr.array().get(ID_identifier));
            if(symb.base_name == "__CPROVER_alloc_size" || symb.base_name == "__CPROVER_alloc")
            {
              continue;
            }
          }
        }

        const codet& assign = target->code;
        const exprt& lhs = assign.op0();
        const exprt& rhs = assign.op1();

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
                    inst_stream << indent <<
                      expr_to_string(a,local_renaming) <<
                      ".set_bit(" << shl <<"," << expr_to_string(b.op0(),local_renaming) << ");\n" ;
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
               
                  inst_stream << indent <<
                    expr_to_string(a, local_renaming) <<
                      ".set_range<" << width  <<  ", " << r <<
                      ">( " <<  expr_to_string(b, local_renaming) << ");\n" ;
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

            inst_stream << indent;
            inst_stream << expr_to_string(index_expr,local_renaming)<<  " =  "
                    << expr_to_string(cst.at(i),local_renaming) <<";"<<endl;
          }
          break;
        }

        inst_stream << indent;
        inst_stream << expr_to_string(target->code.op0(),local_renaming)<<  " =  "
                    << expr_to_string(target->code.op1(),local_renaming) <<";"<<endl;
        break;
      }
      
    case FUNCTION_CALL:
      {
        inst_stream << indent;
        const code_function_callt& code_func = to_code_function_call(to_code(target->code));

        if(code_func.function().id() == ID_symbol)
        {
          irep_idt original_id = code_func.function().get(ID_identifier);

          if(renaming.find(original_id) == renaming.end())
          {
            inst_stream << "// ignoring call to `" << original_id <<"'" << endl;
            break;
          }

          irep_idt renamed_func_id = renaming[original_id];
          assert(renamed_func_id != "");
          if(code_func.lhs().is_not_nil())
            inst_stream << expr_to_string(code_func.lhs(),local_renaming) << " = ";
          inst_stream <<  renamed_func_id << "(";
        }
        else
        {
          assert(code_func.function().id() == ID_dereference);
          if(code_func.lhs().is_not_nil())
            inst_stream << expr_to_string(code_func.lhs(),local_renaming) << " = ";
          inst_stream <<  "( " <<  expr_to_string(code_func.function(),local_renaming) << " )(";
        }
        unsigned i = 0;
        for(; i+1 < code_func.arguments().size(); i++)
        {
          inst_stream << expr_to_string(code_func.arguments()[i],local_renaming) <<", ";
        }
        if(i < code_func.arguments().size())
        {
          inst_stream << expr_to_string(code_func.arguments()[i],local_renaming);
        }
        inst_stream <<");" << endl;
        break;
      }
      
    case SKIP:
      inst_stream << indent << ";" << endl;
      break;

    case LOCATION:
      break;

    case ASSERT:
      inst_stream
        << indent 
        << "assert( " << expr_to_string(target->guard, local_renaming) << ");"
        << endl;
      break;

    case ASSUME:
      break;

    case END_FUNCTION:
      inst_stream <<indent <<"; // END_FUNCTION" << endl;
      break;

    case OTHER:
      {
        const codet& code = to_code(target->code);
        if(code.get_statement() == ID_expression)
        {
          // expression has no sideeffect
          inst_stream << indent << ";\n";
        }
        else if(has_prefix(id2string(code.get_statement()), "assign"))
        {
          if(code.op0().id() == "dynamic_size" ||
             code.op0().id() == "valid_object")
          {
            // shall we do something else?
            break;
          }

          inst_stream << indent;

          std::string statement = id2string(code.get_statement());
          std::string op_str = statement.substr(string("assign").size(), statement.size());

          inst_stream << expr_to_string(target->code.op0(),local_renaming)<<" "<< op_str << "="
                    << expr_to_string(target->code.op1(),local_renaming) <<";"<<endl;
           break;
        }
        else if(code.get_statement() == ID_nondet)
        {
          //ps_irep("code",target->code);
          // todo: random input
          throw "Goto2cpp: 'nondet' is not yet implemented\n";
        }
        else
        {
          //ps_irep("code",target->code);
          throw "Goto2cpp: instruction not yet supported\n";
        }
        break;
      }

    case DECL:
      /* Ignore; implicit_decls finds it */
      break;

    default:
      cerr << target->type << endl;
      //ps_irep("code",target->code);
      assert(0);
    }
  }

  os << decl_stream.str();
  os << inst_stream.str();
}

/*******************************************************************\

Function: goto2cppt::convert_compound_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void goto2cppt::convert_compound_rec(
  const struct_typet &struct_type,
  std::ostream &os)
{
  irep_idt name = renaming[struct_type.get("name")];
  assert( name != "");

  static set<irep_idt> converted;

  if(converted.count(name) == 1)
    return;

  converted.insert(name);

  const irept& bases = struct_type.find("bases");
  string base_decls;
  for(unsigned i = 0; i < bases.get_sub().size(); i++)
  {
    irep_idt base_id = bases.get_sub()[i].find(ID_type).get(ID_identifier);
    assert(base_id != "");

    irep_idt renamed_base_id = renaming[base_id];

    if(converted.count(renamed_base_id) == 0)
    {
      const symbolt& base_symb = ns.lookup(base_id);
      convert_compound_rec(to_struct_type(base_symb.type),os);
    }

    base_decls += id2string(renamed_base_id) + " ";

    if(i+1 < bases.get_sub().size())
      base_decls += ", ";
  }

  string indent(" ");
  string struct_body;
  string constructor_args;
  string constructor_body;

  for(struct_typet::componentst::const_iterator
      it=struct_type.components().begin();
      it!=struct_type.components().end();
      it++)
  {
    const struct_typet::componentt& compo = *it;

    if(compo.type().id() == ID_code)
      continue;

    if(!compo.get_bool("from_base"))
    {

      typet final_type = ns.follow(compo.type());
      if(final_type.id() == ID_struct)
          convert_compound_rec(to_struct_type(final_type),os);
      else if(final_type.id() == ID_array)
      {
        typet final_subtype = ns.follow(final_type.subtype());
        while(final_subtype.id() == ID_array)
        {
          typet tmp = ns.follow(final_subtype.subtype());
          final_subtype.swap(tmp);
        }
        
        if(final_subtype.id() == ID_struct)
          convert_compound_rec(to_struct_type(final_subtype),os);
      }

      irep_idt renamed_compo_id = unique_name(compo.get(ID_base_name));
      renaming[compo.get(ID_name)] = renamed_compo_id;

      struct_body += indent + "// " + id2string(compo.get(ID_name)) + "\n";

      if(compo.type().id() == ID_pointer && compo.type().subtype().id() == ID_code)
      {
        const code_typet& code_type = to_code_type(compo.type().subtype());
        struct_body += indent + type_to_string(code_type.return_type()) +
                       " ( * " + id2string(renamed_compo_id) + ") (";
        unsigned i = 0;
        for(; i+1 < code_type.arguments().size(); i++)
          struct_body += type_to_string(code_type.arguments()[i].type()) + ", ";
        if(i < code_type.arguments().size())
          struct_body += type_to_string(code_type.arguments()[i].type());
        struct_body += ");\n";
      }
      else
      {
        string type_str = type_to_string(compo.type());
        struct_body += indent + type_str + " " + id2string(renamed_compo_id) + ";\n";
      }
    } // end from base

    // for the constructor
    std::string component_name =  renaming[compo.get(ID_name)].as_string();
    assert(component_name != "");

    if(it != struct_type.components().begin()) constructor_args += ", ";

    if(compo.type().id() == ID_pointer)
      constructor_args += type_to_string(compo.type()) + component_name;
    else
      constructor_args += "const " + type_to_string(compo.type()) + "& " + component_name;

    constructor_body += indent + indent + "this->"+component_name + " = " + component_name + ";\n";
  }

  os << "struct " << id2string(name) ;
  if(base_decls != "")
    os << ": " << base_decls;
  os << endl;
  os << "{" << endl;
  os << struct_body;

  if(!struct_type.components().empty())
  {
    os << indent << name << "(){}\n";
    os << indent << "explicit " << name
       << "(" + constructor_args + ")\n";
    os << indent << "{\n";
    os << constructor_body;
    os << indent << "}\n";
  }

  os << "};" << endl;
  os << endl;
}

/*******************************************************************\

Function: goto2cppt::type_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

string goto2cppt::type_to_string(const typet& type, bool keep_int)
{
  string ret;

  if(type.id() == ID_bool)
    ret = "bool ";
  else if(type.id() == ID_signedbv)
  {
    if(keep_int)
    {
      unsigned width = atoi(type.get(ID_width).c_str());
      if(width == config.ansi_c.int_width)
        return "int ";
      else if(width == config.ansi_c.char_width)
        return "char ";
      else if(width == config.ansi_c.long_int_width)
        return "long int ";
      else if(width == config.ansi_c.short_int_width)
        return "short int ";
      else if(width == config.ansi_c.long_long_int_width)
        return "long long int";
      else if(width == config.ansi_c.double_width)
        return "double ";
    }
    return "__signedbv<" + id2string(type.get("width")) + "> ";
  }
  else if(type.id() == ID_unsignedbv)
  {
    if(keep_int)
    {
      unsigned width = atoi(type.get(ID_width).c_str());
      if(width == config.ansi_c.int_width)
        return "unsigned int ";
      else if(width == config.ansi_c.char_width)
        return "unsigned char ";
      else if(width == config.ansi_c.long_int_width)
        return "unsigned long int ";
      else if(width == config.ansi_c.short_int_width)
        return "unsigned short int ";
      else if(width == config.ansi_c.long_long_int_width)
        return "unsigned long long int";
    }
    return "__unsignedbv<" + id2string(type.get(ID_width)) + "> ";
  }
  else if(type.id() == ID_fixedbv)
  {
    return "double";
  }
  else if(type.id() == ID_pointer)
  {
    if(type.subtype().id() == ID_code)
    {
      std::map<typet,irep_idt>::const_iterator tdit =
        typedef_map.find(type);

      if(tdit != typedef_map.end())
      {
        ret = tdit->second.as_string()+" ";
      }
      else
      {
        const code_typet& code_type = to_code_type(type.subtype());

        irep_idt typedef_name = unique_name("typedef_func_ptr");

        typedef_stream << "typedef "
                      << type_to_string(code_type.return_type())
                      << "(* "
                      << typedef_name
                      << ")(";

        unsigned i = 0;
        for(; i+1 < code_type.arguments().size(); i++)
        {
          typedef_stream << type_to_string(code_type.arguments()[i].type())
                         << ", ";
        }

        if(i < code_type.arguments().size())
          typedef_stream << type_to_string(code_type.arguments()[i].type());
        typedef_stream << ")";

        typedef_map[type] = typedef_name;
        typedef_stream << ";" << std::endl;
        ret = typedef_name.as_string()+" ";
      }
    }
    else
    {
      ret += " " +type_to_string(type.subtype());
      /*if(type.get_bool("#constant"))
        ret += "const ";*/
      ret += "* ";
    }
  }
  else if(type.id() == ID_symbol)
  {
    map<irep_idt,irep_idt>::const_iterator it_ren =
      renaming.find(type.get(ID_identifier));
    if(it_ren == renaming.end())
    {
      const symbolt& symb = ns.lookup(type.get(ID_identifier));
      assert(symb.is_type);
      ret = type_to_string(symb.type);
    }
    else
      ret = id2string(it_ren->second) + " ";
  }
  else if(type.id() == ID_verilogbv)
  {
    return "__verilogbv<" + id2string(type.get(ID_width)) + "> ";
  }
  else if(type.id() == ID_c_enum)
  {
    ret = "__signedbv<"+i2string(config.ansi_c.int_width)+">";
  }
  else if(type.id() == ID_empty)
  {
    ret = "void ";
  }
  else if(type.id() == ID_constructor ||
          type.id() == ID_destructor)
  {
    ret = "void ";
  }
  else if(type.id() == ID_array)
  {
    const array_typet& array_type = to_array_type(type);

    std::string subtype = type_to_string(type.subtype());

    map<irep_idt,irep_idt> dummy_renaming; 
    std::string size =
      expr_to_string(array_type.size(),dummy_renaming,true);

    return "__array<" + subtype + " , " + size + " > ";
    std::map<typet,irep_idt>::const_iterator tdit =
        typedef_map.find(type);
  }
  else if(type.id() == ID_struct)
  {
    map<irep_idt,irep_idt>::const_iterator it_ren =
      renaming.find(type.get(ID_name));
    assert(it_ren != renaming.end());
    ret = id2string(it_ren->second) + " ";
  }
  else
  {
    std::cerr << id2string(type.id()) << endl;
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

Function: goto2cppt::expr_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

string goto2cppt::expr_to_string(
  const exprt &expr,
  const map<irep_idt,irep_idt> &local_renaming,
  bool keep_int)
{
  if(expr.id() == ID_symbol)
  {
    map<irep_idt,irep_idt>::const_iterator it_loc =
      local_renaming.find(expr.get(ID_identifier));

    if(it_loc != local_renaming.end())
      return id2string(it_loc->second);

    map<irep_idt,irep_idt>::const_iterator it_glob =
      renaming.find(expr.get(ID_identifier));

    if(it_glob != renaming.end())
      return id2string(it_glob->second);
  }
  else if(expr.id() == ID_member)
  {
    irep_idt renamed_id = renaming[expr.get(ID_component_name)];
    assert(renamed_id != "");
    return expr_to_string(expr.op0(),local_renaming) + "." + id2string(renamed_id) ;
  }
  else if(expr.id() == ID_dereference)
  {
    return "(* " + expr_to_string(expr.op0(),local_renaming) + ")";
  }
  else if(expr.id() == "+" ||
          expr.id() == "-" ||
          expr.id() == "*")
  {
    assert(expr.operands().size() >= 2 );

    std::string str;

    if(
        expr.op0().type().id() == ID_pointer ||
        expr.op1().type().id() == ID_pointer ||
        expr.op0().id() == ID_symbol ||
        expr.op0().id() == ID_constant ||
        expr.op0().id() == ID_member ||
        expr.op0().id() == ID_index ||
        expr.op0().id() == ID_dereference)
    {
      str = "("+ expr_to_string(expr.operands()[0],local_renaming) +
            expr.id().as_string() + expr_to_string(expr.operands()[1],local_renaming) +")";
    }
    else
      str = expr_to_string(expr.operands()[0],local_renaming) 
            + expr.id().as_string() + "=" + expr_to_string(expr.operands()[1],local_renaming);

    for(unsigned i = 2; i < expr.operands().size(); i++ )
    {
       const exprt& opleft = expr.operands()[i-1];
       const exprt& opright = expr.operands()[i];

       if( opleft.type().id() == ID_pointer ||
           opright.type().id() == ID_pointer)
        str += expr.id().as_string() + expr_to_string(expr.operands()[i],local_renaming);
       else
        str += expr.id().as_string() +"=" + expr_to_string(expr.operands()[i],local_renaming);
    }
    str = "(" + str + ")";
    return str;
  }
  else if(expr.id() == "*"   || expr.id() == "/" ||
          expr.id() == "<"   || expr.id() == ">" ||
          expr.id() == "<="  ||
          expr.id() == ">=")
  {
    assert(expr.operands().size() == 2);
    return "(" + expr_to_string(expr.op0(),local_renaming) + id2string(expr.id())
         + expr_to_string(expr.op1(),local_renaming) + ")";
  }
  else if(expr.id() == ID_mod)
  {
    assert(expr.operands().size() == 2);
    return "(" + expr_to_string(expr.op0(),local_renaming) + "%"
         + expr_to_string(expr.op1(),local_renaming) + ")";
  }
  else if(expr.id() == ID_equal)
  {
    assert(expr.operands().size() == 2);
    return "(" + expr_to_string(expr.op0(),local_renaming) +" == " + expr_to_string(expr.op1(),local_renaming) + ")";
  }
  else if(expr.id() == ID_notequal)
  {
    assert(expr.operands().size() == 2);
    return "(" + expr_to_string(expr.op0(),local_renaming) +" != " + expr_to_string(expr.op1(),local_renaming) + ")";
  }
  else if(expr.id() == ID_and)
  {
    assert(expr.operands().size() >= 2);
    std::string str = "( ";
    str +=  expr_to_string(expr.operands()[0],local_renaming);
    for(unsigned i = 1; i < expr.operands().size(); i++ )
      str += " && " + expr_to_string(expr.operands()[i],local_renaming);
    str += ")";
    return str;
  }
  else if(expr.id() == ID_or)
  {
    assert(expr.operands().size() >= 1);
    std::string str = "( ";
    str +=  expr_to_string(expr.operands()[0],local_renaming);
    for(unsigned i = 1; i < expr.operands().size(); i++ )
      str += " || " + expr_to_string(expr.operands()[i],local_renaming);
    str += ")";
    return str;
  }
  else if(expr.id() == ID_not)
  {
    assert(expr.operands().size() == 1);
    return "(!" + expr_to_string(expr.op0(),local_renaming) + ")";
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
      str = "("+ expr_to_string(expr.operands()[0],local_renaming) +
            " & " + expr_to_string(expr.operands()[1],local_renaming) +")";
    }
    else
      str = expr_to_string(expr.operands()[0],local_renaming)
            + " &= " + expr_to_string(expr.operands()[1],local_renaming);

    for(unsigned i = 2; i < expr.operands().size(); i++ )
      str += " &= " + expr_to_string(expr.operands()[i],local_renaming);
    str = "(" + str + ")";
    return str;
  }
  else if(expr.id() == ID_bitor)
  {
    assert(expr.operands().size() >= 2);

    std::string str;

    if(expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      str = "("+ expr_to_string(expr.operands()[0],local_renaming) +
            " | " + expr_to_string(expr.operands()[1],local_renaming) +")";
    }
    else
      str = expr_to_string(expr.operands()[0],local_renaming)
            + " |= " + expr_to_string(expr.operands()[1],local_renaming);

    for(unsigned i = 2; i < expr.operands().size(); i++ )
      str += " |= " + expr_to_string(expr.operands()[i],local_renaming);
    str = "(" + str + ")";
    return str;

  }
  else if(expr.id() == ID_bitxor)
  {
    std::string str;
    
    if(expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      str = "("+ expr_to_string(expr.operands()[0],local_renaming) +
            " ^ " + expr_to_string(expr.operands()[1],local_renaming) +")";
    }
    else
      str = expr_to_string(expr.operands()[0],local_renaming)
            + " ^= " + expr_to_string(expr.operands()[1],local_renaming);
    for(unsigned i = 2; i < expr.operands().size(); i++ )
      str += " ^= " + expr_to_string(expr.operands()[i],local_renaming);
    str = "(" + str + ")";
    return str;
  }
  else if(expr.id() == ID_bitnot)
  {
    assert(expr.operands().size() == 1);
    return "(~ " + expr_to_string(expr.op0(),local_renaming) + ")";
  }
  else if(expr.id() == ID_shl)
  {
    assert(expr.operands().size() == 2);

    std::string shf_str;
    if(expr.op1().id() == ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv || expr.op1().type().id() == ID_signedbv);
      string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)),2);
      shf_str = integer2string(cst, 10);
      assert(shf_str != "");
    }
    else
      shf_str =  expr_to_string(expr.op1(),local_renaming) + ".to_int()";

    if(expr.op0().id() == ID_symbol ||
       expr.op0().id() == ID_constant ||
       expr.op0().id() == ID_member ||
       expr.op0().id() == ID_index ||
       expr.op0().id() == ID_dereference)
    {
      return "(" + expr_to_string(expr.op0(),local_renaming) +" << " + shf_str + " )";
    }
    return "(" + expr_to_string(expr.op0(),local_renaming) +" <<= " + shf_str + " )";
  }

  else if(expr.id() == ID_lshr || expr.id() == ID_ashr)
  {
    assert(expr.operands().size() == 2);

    if(expr.op1().id() == ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv || expr.op1().type().id() == ID_signedbv);
      string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)),2);
      string str = integer2string(cst, 10);
      assert(str != "");
      return "(" + expr_to_string(expr.op0(),local_renaming) +" >> "+str + " )";
    }

    return "(" + expr_to_string(expr.op0(),local_renaming) +" >> " + expr_to_string(expr.op1(),local_renaming) + ".to_int() )";
  }
  else if(expr.id() == ID_unary_minus)
  {
    assert(expr.operands().size() == 1);
    return "( " + type_to_string(expr.op0().type())+"(0) - "  + expr_to_string(expr.op0(),local_renaming) + " ) ";
  }
  else if(expr.id() == ID_constant)
  {
    if(expr.type().id() == ID_signedbv ||
       expr.type().id() == ID_unsignedbv)
    {
      string width_str = id2string(expr.type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);

      if(keep_int)
      {
        mp_integer cst = string2integer(id2string(expr.get(ID_value)),2);
        string str = integer2string(cst, 10);
        assert(str != "");
        return str;
      }

      if(width <= config.ansi_c.int_width)
      {
        mp_integer cst = string2integer(id2string(expr.get(ID_value)),2);
        string str = integer2string(cst, 10) ;
        assert(str != "");
        return "__" + id2string(expr.type().id()) + "<" + width_str + "> ( " + str +")";
      }
      else
      {
        std::string type_id = "__" + id2string(expr.type().id()) + "<" +width_str + ">";
        return id2string(get_global_constant(id2string(expr.get(ID_value)), type_id));
      }
    }

    if(expr.type().id() == ID_bool)
      return id2string(expr.get(ID_value));

    if(expr.type().id() == ID_pointer)
    {
      assert(expr.get(ID_value) == "NULL");
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
        string width_str = id2string(expr.type().get(ID_width));
        mp_integer width = string2integer(width_str,10);
        assert(width != 0);
        std::string type_id = "__" + id2string(expr.type().id()) + "<" +width_str + ">";
        return  type_id +"("+ id2string(get_global_constant(expr.get("value"), type_id))+")";
      }
    }

    if(expr.type().id() == ID_c_enum)
    {
      string str = "__signedbv<" + id2string(expr.type().get(ID_width)) +
        "> (" + id2string(expr.get(ID_value)) + ")";
      return str;
    }

    if(expr.type().id() == ID_symbol)
    {
      typet final_type = ns.follow(expr.type());
      exprt expr2(expr);
      expr2.type() = final_type;
      return expr_to_string(expr2,local_renaming);
    }
  }
  else if(expr.id() == ID_typecast)
  {
    assert(expr.operands().size() == 1);
    if(expr.type().id() == ID_bool)
      return "( "+ expr_to_string(expr.op0(),local_renaming) + ".to_bool())";

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
        set<irep_idt> bases;
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
                 expr_to_string(expr.op0(),local_renaming) + ")";
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
                 expr_to_string(expr.op0(),local_renaming) + ")";
        }

        std::cerr << "Warning conversion from " << op_subtype.get("name")
                  << " to " << subtype.get(ID_name) << " is not safe!\n";

      }
    }

    return "((" + type_to_string(expr.type()) + ") " +
           expr_to_string(expr.op0(),local_renaming) + ")";
  }
  else if(expr.id() == ID_address_of)
  {
    assert(expr.operands().size() == 1);
    return "(&" + expr_to_string(expr.op0(),local_renaming) + ")";
  }
  else if(expr.id() == ID_index)
  {
    assert(expr.operands().size() == 2);

    if(expr.op1().id() == ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv || expr.op1().type().id() == ID_signedbv);
      string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)), 2);
      string str = integer2string(cst, 10);
      assert(str != "");
      return "(" +expr_to_string(expr.op0(),local_renaming) + "[" + str + " ] )";
    }

    return "(" +expr_to_string(expr.op0(),local_renaming) +
           "[" + expr_to_string(expr.op1(),local_renaming) + ".to_int() ] )";
  }
  else if(expr.id() == ID_extractbits)
  {
    assert(expr.operands().size()==3);

    return "__" + id2string(expr.type().id())+"<"+ id2string(expr.type().get(ID_width)) + "> ("
           + expr_to_string(expr.op0(),local_renaming) + ", "
           + expr_to_string(expr.op1(),local_renaming,true) + ", "
           + expr_to_string(expr.op2(),local_renaming,true) + " )";
  }
  else if(expr.id() == ID_extractbit)
  {
    assert(expr.operands().size()==2);

    if(expr.op1().id() == ID_constant)
    {
      assert(expr.op1().type().id() == ID_unsignedbv || expr.op1().type().id() == ID_signedbv);
      string width_str = id2string(expr.op1().type().get(ID_width));
      mp_integer width = string2integer(width_str,10);
      assert(width != 0);
      mp_integer cst = string2integer(id2string(expr.op1().get(ID_value)),2);
      string str = integer2string(cst, 10);
      assert(str != "");
      return "((" + expr_to_string(expr.op0(),local_renaming) + ")[ "+ str + " ])";
    }

    return "((" + expr_to_string(expr.op0(),local_renaming) + ")[ "
           + expr_to_string(expr.op1(),local_renaming,true) + " ])";
  }
  else if(expr.id() == ID_sideeffect)
  {
    if(expr.get(ID_statement) == ID_cpp_new)
    {
      assert(expr.type().id() == ID_pointer);
      return "new " + type_to_string(expr.type().subtype())+ "()";
    }
    else if(expr.get(ID_statement) == "cpp_new[]")
    {
        assert(expr.type().id() == ID_pointer);
        return "(new " + type_to_string(expr.type().subtype()) +
               "[ " + expr_to_string((const exprt &)expr.find(ID_size), local_renaming) + ".to_int()])";
    }
    else if(expr.get(ID_statement) == "nondet")
    {
      return "__nondet<"+type_to_string(expr.type())+ " >()";
    }
  }
  else if(expr.id() == ID_string_constant)
  {
    string get_value = expr.get(ID_value).as_string();
    string filtered_value;
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
  else if(expr.id() == ID_if)
  {
    assert(expr.operands().size() == 3);
    return "("+ expr_to_string(expr.op0(),local_renaming)+ "? "+ expr_to_string(expr.op1(),local_renaming) +
           ": " + expr_to_string(expr.op2(),local_renaming) + ")";
  }
  else if(expr.id() == ID_infinity)
  {
    return "CPROVER_INFINITY";
  }
  else if(expr.id() == ID_concatenation)
  {
    return "__concatenation( "
           + expr_to_string(expr.op0(),local_renaming)
           + ", " + expr_to_string(expr.op1(),local_renaming)
           + ")";
  }
  else if(expr.id() == ID_with)
  {
    assert(expr.operands().size() == 3);

    if(expr.op0().type().id() == ID_array)
    {
      std::string T = type_to_string(expr.type().subtype());
      std::string W = expr_to_string(
          to_array_type(expr.type()).size(),local_renaming,true);

      std::string src = expr_to_string(expr.op0(),local_renaming);
      std::string index = expr_to_string(expr.op1(),local_renaming);
      std::string value = expr_to_string(expr.op2(),local_renaming);

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
      const typet& t = ns.follow(expr.type());
      assert(t.id() == ID_struct);
      std::string src = expr_to_string(expr.op0(),local_renaming);
      std::string value = expr_to_string(expr.op2(),local_renaming);
      std::string member =
        renaming[expr.get(ID_component_name)].as_string();
      std::string type =
        renaming[t.get(ID_name)].as_string();

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
    std::string W =  expr_to_string(
      to_array_type(expr.type()).size(),local_renaming,true);
    std::string arg = expr_to_string(expr.op0(),local_renaming);
    return "__array<" + T + ", " + W + " >("+ arg + ")";
  }
  else if(expr.id() == ID_struct)
  {
    const struct_typet& struct_type = 
      to_struct_type(ns.follow(expr.type()));
    const struct_typet::componentst& components = struct_type.components();
    const exprt::operandst& operands = expr.operands();


    string ret = renaming[struct_type.get(ID_name)].as_string() + "(";
    
    assert(operands.size() == components.size());
    if( 0 < operands.size())
    {
      assert(operands[0].type() == components[0].type());
      ret += expr_to_string(operands[0],local_renaming);
    }

    for(unsigned i = 1; i < operands.size(); i++)
    {
      assert(operands[i].type() == components[i].type());
      ret += ", " +expr_to_string(operands[i],local_renaming);
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

string goto2cppt::implicit_declarations(
  const exprt &expr,
  map<irep_idt,irep_idt> &local_renaming)
{
  std:: string ret;
  if(expr.id() == ID_symbol)
  {
    map<irep_idt,irep_idt>::const_iterator it_glob =
      renaming.find(expr.get(ID_identifier));
    
    if(it_glob == renaming.end())
    {

      map<irep_idt,irep_idt>::const_iterator it_loc =
        local_renaming.find(expr.get(ID_identifier));

      if(it_loc == local_renaming.end())
      {
        const symbolt& symb = ns.lookup(expr.get(ID_identifier));
        if(symb.type.id() != ID_code)
        {
          // not yet declared
          irep_idt renamed_id = unique_name(symb.base_name);
          local_renaming[symb.name] = renamed_id;
          ret += "  " + type_to_string(symb.type)
                      + " " + renamed_id.as_string()  + ";\n";
        }
      }
    }
   }
  else
  {
    for(unsigned i = 0; i < expr.operands().size(); i++)
    {
      ret += implicit_declarations(expr.operands()[i], local_renaming);
    }
  }
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
  #if 0
  forall_goto_functions(it, src)
    if(it->second.body_available &&
       it->first!=ID_main)
      dump_c(it, ns, out);
  #endif

  goto2cppt goto2cpp(ns, src, out);
  goto2cpp.convert(out);
}

