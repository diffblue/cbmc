/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <util/config.h>
#include <util/prefix.h>
#include <util/find_symbols.h>
#include <util/base_type.h>
#include <util/i2string.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include "goto_program2code.h"
#include "dump_c_class.h"

#include "dump_c.h"

/*******************************************************************\

Function: operator<<

Inputs:

Outputs:

Purpose:

\*******************************************************************/

inline std::ostream &operator << (std::ostream &out, dump_ct &src)
{
  src(out);
  return out;
}

/*******************************************************************\

Function: dump_ct::operator()

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::operator()(std::ostream &os)
{
  std::stringstream func_decl_stream;
  std::stringstream compound_body_stream;
  std::stringstream global_var_stream;
  std::stringstream func_body_stream;
  local_static_declst local_static_decls;
  hash_map_cont<irep_idt, irep_idt, irep_id_hash> original_tags;

  // add copies of struct types when ID_C_transparent_union is only
  // annotated to parameter
  symbol_tablet symbols_transparent;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    symbolt &symbol=it->second;

    if(symbol.type.id()!=ID_code) continue;

    code_typet &code_type=to_code_type(symbol.type);
    code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::iterator
        it2=parameters.begin();
        it2!=parameters.end();
        ++it2)
    {
      typet &type=it2->type();

      if(type.id()==ID_symbol &&
         type.get_bool(ID_C_transparent_union))
      {
        symbolt new_type_sym=
          ns.lookup(to_symbol_type(type).get_identifier());

        new_type_sym.name=id2string(new_type_sym.name)+"$transparent";
        new_type_sym.type.set(ID_C_transparent_union, true);

        // we might have it already, in which case this has no effect
        symbols_transparent.add(new_type_sym);

        to_symbol_type(type).set_identifier(new_type_sym.name);
        type.remove(ID_C_transparent_union);
      }
    }
  }
  forall_symbols(it, symbols_transparent.symbols)
    copied_symbol_table.add(it->second);

  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> unique_tagst;
  unique_tagst unique_tags;

  // add tags to anonymous union/struct,
  // and prepare lexicographic order
  std::set<std::string> symbols_sorted;
  Forall_symbols(it, copied_symbol_table.symbols)
  {
    symbolt &symbol=it->second;

    if((symbol.type.id()==ID_union || symbol.type.id()==ID_struct) &&
       symbol.type.get(ID_tag).empty())
    {
      assert(symbol.is_type);
      symbol.type.set(ID_tag, ID_anonymous);
    }

    const std::string name_str=id2string(it->first);
    if(symbol.is_type && !symbol.type.get(ID_tag).empty())
    {
      irep_idt original_tag=symbol.type.get(ID_tag);
      original_tags[it->first]=original_tag;
      std::string new_tag=id2string(original_tag);

      std::string::size_type tag_pos=new_tag.rfind("tag-");
      if(tag_pos!=std::string::npos)
      {
        new_tag.erase(0, tag_pos+4);
        symbol.type.set(ID_tag, new_tag);
      }

      std::pair<unique_tagst::iterator, bool> unique_entry=
        unique_tags.insert(std::make_pair(symbol.type.get(ID_tag), 0));
      if(!unique_entry.second)
      {
        do
        {
          symbol.type.set(
            ID_tag,
            new_tag+"$"+i2string(unique_entry.first->second));
          ++(unique_entry.first->second);
        }
        while(!unique_tags.insert(std::make_pair(
              symbol.type.get(ID_tag), 0)).second);
      }
    }

    if(!symbols_sorted.insert(name_str).second)
      assert(false);
  }

  // collect all declarations we might need, include local static variables
  bool skip_function_main=false;
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.is_type &&
        (symbol.type.id()==ID_struct ||
         symbol.type.id()==ID_incomplete_struct ||
         symbol.type.id()==ID_union ||
         symbol.type.id()==ID_incomplete_union))
    {
      if(symbol.location.get_function().empty())
      {
        os << "// " << symbol.name << std::endl;
        os << "// " << symbol.location << std::endl;
        os << type_to_string(symbol.type) << ";" << std::endl;
        os << std::endl;
      }
    }
    else if(symbol.is_static_lifetime && symbol.type.id()!=ID_code)
      convert_global_variable(
          symbol,
          global_var_stream,
          local_static_decls,
          original_tags);
    else if(symbol.type.id()==ID_code)
    {
      goto_functionst::function_mapt::const_iterator func_entry=
        goto_functions.function_map.find(symbol.name);

      if(func_entry!=goto_functions.function_map.end() &&
         func_entry->second.body_available &&
         (symbol.name=="c::main" ||
          (!config.main.empty() && symbol.name==config.main)))
        skip_function_main=true;
    }
  }

  // function declarations and definitions
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.type.id()!=ID_code) continue;

    convert_function_declaration(
      symbol,
      skip_function_main,
      func_decl_stream,
      func_body_stream,
      local_static_decls,
      original_tags);
  }

  // (possibly modified) compound types
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.is_type &&
        (symbol.type.id()==ID_struct ||
         symbol.type.id()==ID_incomplete_struct ||
         symbol.type.id()==ID_union ||
         symbol.type.id()==ID_incomplete_union))
      convert_compound_declaration(
          symbol,
          compound_body_stream);
  }

  os << std::endl;
  for(std::set<std::string>::const_iterator
      it=system_headers.begin();
      it!=system_headers.end();
      ++it)
    os << "#include <" << *it << ">" << std::endl;
  if(!system_headers.empty()) os << std::endl;

  os << "#ifndef NULL" << std::endl
     << "#define NULL ((void*)0)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef FENCE" << std::endl
     << "#define FENCE(x) ((void)0)" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef IEEE_FLOAT_EQUAL" << std::endl
     << "#define IEEE_FLOAT_EQUAL(x,y) ((x)==(y))" << std::endl
     << "#endif" << std::endl;
  os << "#ifndef IEEE_FLOAT_NOTEQUAL" << std::endl
     << "#define IEEE_FLOAT_NOTEQUAL(x,y) ((x)!=(y))" << std::endl
     << "#endif" << std::endl;

  os << std::endl;

  os << func_decl_stream.str();
  os << std::endl;
  os << compound_body_stream.str();
  os << std::endl;

#if 0
  os << global_constant_stream.str();
  global_constant_stream.clear();
#endif

  os << global_var_stream.str();
  os << std::endl;
  os << func_body_stream.str();
}

/*******************************************************************\

Function: dump_ct::convert_compound_declarations

Inputs:

Outputs:

Purpose: declare compound types

\*******************************************************************/

void dump_ct::convert_compound_declaration(
    const symbolt &symbol,
    std::ostream &os_body)
{
  if(!symbol.location.get_function().empty())
    return;

  // do compound type body
  if(symbol.type.id()!=ID_incomplete_struct &&
      symbol.type.id()!=ID_incomplete_union)
    convert_compound(
        to_struct_union_type(symbol.type),
        true,
        os_body);
}

/*******************************************************************\

Function: dump_ct::convert_compound

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_compound(
  const typet &type,
  bool recursive,
  std::ostream &os)
{
  if(type.id()==ID_symbol)
    convert_compound(ns.follow(type), recursive, os);
  else if(type.id()==ID_array || type.id()==ID_pointer)
  {
    if(!recursive) return;

    convert_compound(type.subtype(), recursive, os);

    // sizeof may contain a type symbol that has to be declared first
    if(type.id()==ID_array)
    {
      find_symbols_sett syms;
      find_type_symbols(to_array_type(type).size(), syms);

      for(find_symbols_sett::const_iterator
          it=syms.begin();
          it!=syms.end();
          ++it)
        convert_compound(symbol_typet(*it), recursive, os);
    }
  }
  else if(type.id()==ID_struct || type.id()==ID_union)
    convert_compound(to_struct_union_type(type), recursive, os);
}

/*******************************************************************\

Function: dump_ct::convert_compound

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_compound(
  const struct_union_typet &type,
  bool recursive,
  std::ostream &os)
{
  const irep_idt &name=type.get(ID_tag);

  if(!converted.insert(name).second)
    return;

  const irept &bases = type.find(ID_bases);
  std::stringstream base_decls;
  forall_irep(parent_it, bases.get_sub())
  {
    assert(false);
    /*
    assert(parent_it->id() == ID_base);
    assert(parent_it->get(ID_type) == ID_symbol);

    const irep_idt &base_id=
      parent_it->find(ID_type).get(ID_identifier);
    const irep_idt &renamed_base_id=global_renaming[base_id];
    const symbolt &parsymb=ns.lookup(renamed_base_id);

    convert_compound_rec(parsymb.type, os);

    base_decls << id2string(renamed_base_id) +
      (parent_it+1==bases.get_sub().end()?"":", ");
      */
  }

  /*
  // for the constructor
  string constructor_args;
  string constructor_body;

  std::string component_name =  id2string(renaming[compo.get(ID_name)]);
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
      it=type.components().begin();
      it!=type.components().end();
      it++)
  {
    const struct_typet::componentt &comp=*it;
    typet comp_type=ns.follow(comp.type());

    if(comp_type.id()==ID_code ||
       comp.get_bool(ID_from_base) ||
       comp.get_is_padding())
      continue;

    if(recursive && comp_type.id()!=ID_pointer)
      convert_compound(comp_type, recursive, os);

    irep_idt comp_name=comp.get_name();

    struct_body << indent(1) << "// " << comp_name << std::endl;
    struct_body << indent(1);

    // component names such as "main" would collide with other objects in the
    // namespace
    std::string fake_unique_name="NO/SUCH/NS::"+id2string(comp_name);
    std::string s=make_decl(fake_unique_name, comp_type);
    assert(s.find("NO/SUCH/NS")==std::string::npos);

    if(comp.get_is_bit_field() &&
       ((comp_type.id()!=ID_c_enum &&
         to_bitvector_type(comp_type).get_width()==0) ||
        (comp_type.id()==ID_c_enum &&
         to_bitvector_type(comp_type.subtype()).get_width()==0)))
    {
      comp_name="";
      s=type_to_string(comp_type);
    }

    if(s.find("__CPROVER_bitvector")==std::string::npos)
    {
      struct_body << s;
      if(comp.get_is_bit_field() && comp_type.id()!=ID_c_enum)
        struct_body << " : " << to_bitvector_type(comp_type).get_width();
      else if(comp.get_is_bit_field() && comp_type.id()==ID_c_enum)
        struct_body << " : " << to_bitvector_type(comp_type.subtype()).get_width();
    }
    else if(comp_type.id()==ID_signedbv)
    {
      const signedbv_typet &t=to_signedbv_type(comp_type);
      if(t.get_width()<=config.ansi_c.long_long_int_width)
        struct_body << "long long int " << comp_name
          << " : " << t.get_width();
      else if(language->id()=="cpp")
        struct_body << "__signedbv<" << t.get_width() << "> "
          << comp_name;
      else
        struct_body << s;
    }
    else if(comp_type.id()==ID_unsignedbv)
    {
      const unsignedbv_typet &t=to_unsignedbv_type(comp_type);
      if(t.get_width()<=config.ansi_c.long_long_int_width)
        struct_body << "unsigned long long " << comp_name
          << " : " << t.get_width();
      else if(language->id()=="cpp")
        struct_body << "__unsignedbv<" << t.get_width() << "> "
          << comp_name;
      else
        struct_body << s;
    }
    else
      assert(false);

    struct_body << ";" << std::endl;
  }

  os << type_to_string(type);
  if(!base_decls.str().empty())
  {
    assert(language->id()=="cpp");
    os << ": " << base_decls.str();
  }
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

  os << "}";
  if(type.get_bool(ID_C_transparent_union))
    os << " __attribute__ ((__transparent_union__))";
  if(type.get_bool(ID_C_packed))
    os << " __attribute__ ((__packed__))";
  os << ";";
  os << std::endl;
  os << std::endl;
}

/*******************************************************************\

Function: dump_ct::supress

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool dump_ct::ignore(const irep_idt &identifier)
{
  return (has_prefix(id2string(identifier), "c::__CPROVER_") ||
     identifier=="c::__func__" ||
     identifier=="c::__FUNCTION__" ||
     identifier=="c::__PRETTY_FUNCTION__" ||
     identifier=="c::argc'" ||
     identifier=="c::argv'" ||
     identifier=="c::envp'" ||
     identifier=="c::envp_size'");
}

/*******************************************************************\

Function: dump_ct::cleanup_decl

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::cleanup_decl(
  code_declt &decl,
  std::list<irep_idt> &local_static,
  std::list<irep_idt> &local_type_decls,
  const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  exprt value=nil_exprt();

  if(decl.operands().size()==2)
  {
    value=decl.op1();
    decl.operands().resize(1);
  }

  goto_programt tmp;
  goto_programt::targett t=tmp.add_instruction(DECL);
  t->code=decl;

  if(value.is_not_nil())
  {
    t=tmp.add_instruction(ASSIGN);
    t->code=code_assignt(decl.op0(), value);
  }

  tmp.add_instruction(END_FUNCTION);

  code_blockt b;
  goto_program2codet p2s(
    irep_idt(),
    tmp,
    copied_symbol_table,
    original_tags,
    b,
    local_static,
    local_type_decls,
    system_headers);
  p2s();

  assert(b.operands().size()==1);
  decl.swap(b.op0());
}

/*******************************************************************\

Function: dump_ct::convert_global_variables

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_global_variable(
    const symbolt &symbol,
    std::ostream &os,
    local_static_declst &local_static_decls,
    const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  // we suppress some declarations
  if(ignore(symbol.name))
    return;

  const irep_idt &func=symbol.location.get_function();
  if((func.empty() || symbol.is_extern || symbol.value.is_not_nil()) &&
      !converted.insert(symbol.name).second)
    return;

  code_declt d(symbol.symbol_expr());

  find_symbols_sett syms;
  if(symbol.value.is_not_nil())
    find_symbols(symbol.value, syms);

  // add a tentative declaration to cater for symbols in the initializer
  // relying on it this symbol
  if((func.empty() || symbol.is_extern) &&
     (symbol.value.is_nil() || !syms.empty()))
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;
    os << expr_to_string(d) << std::endl;
  }

  if(!symbol.value.is_nil())
  {
    std::set<std::string> symbols_sorted;
    for(find_symbols_sett::const_iterator
        it=syms.begin();
        it!=syms.end();
        ++it)
      if(!symbols_sorted.insert(id2string(*it)).second)
        assert(false);

    for(std::set<std::string>::const_iterator
        it=symbols_sorted.begin();
        it!=symbols_sorted.end();
        ++it)
    {
      const symbolt &sym=ns.lookup(*it);
      if(!sym.is_type && sym.is_static_lifetime && sym.type.id()!=ID_code)
        convert_global_variable(sym, os, local_static_decls, original_tags);
    }

    d.copy_to_operands(symbol.value);
  }

  if(!func.empty() && !symbol.is_extern)
    local_static_decls[symbol.name]=d;
  else if(!symbol.value.is_nil())
  {
    os << "// " << symbol.name << std::endl;
    os << "// " << symbol.location << std::endl;

    std::list<irep_idt> empty_static, empty_types;
    cleanup_decl(d, empty_static, empty_types, original_tags);
    assert(empty_static.empty());
    os << expr_to_string(d) << std::endl;
  }
}

/*******************************************************************\

Function: dump_ct::convert_function_declarations

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::convert_function_declaration(
    const symbolt& symbol,
    const bool skip_main,
    std::ostream &os_decl,
    std::ostream &os_body,
    local_static_declst &local_static_decls,
    const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  if(ignore(symbol.name))
    return;

  // don't dump artificial main
  if(skip_main && symbol.name==ID_main)
    return;

  // don't dump GCC builtins
  if((symbol.location.get_file()=="gcc_builtin_headers_alpha.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_arm.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_ia32.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_mips.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_power.h" ||
      symbol.location.get_file()=="gcc_builtin_headers_generic.h") &&
     has_prefix(id2string(symbol.name), "c::__builtin_"))
    return;

  if(symbol.name=="c::__builtin_va_start" ||
     symbol.name=="c::__builtin_va_end" ||
     has_prefix(id2string(symbol.name), id2string(ID_gcc_builtin_va_arg)))
  {
    system_headers.insert("stdarg.h");
    return;
  }

  // convert the goto program back to code - this might change
  // the function type
  goto_functionst::function_mapt::const_iterator func_entry=
    goto_functions.function_map.find(symbol.name);
  if(func_entry!=goto_functions.function_map.end() &&
     func_entry->second.body_available)
  {
    code_blockt b;
    std::list<irep_idt> type_decls, local_static;

    goto_program2codet p2s(
      symbol.name,
      func_entry->second.body,
      copied_symbol_table,
      original_tags,
      b,
      local_static,
      type_decls,
      system_headers);
    p2s();

    insert_local_static_decls(
      b,
      local_static,
      local_static_decls,
      type_decls,
      original_tags);

    convertedt converted_bak(converted);
    insert_local_type_decls(
      b,
      type_decls);
    converted.swap(converted_bak);

    os_body << "// " << symbol.name << std::endl;
    os_body << "// " << symbol.location << std::endl;
    os_body << make_decl(symbol.name, symbol.type) << std::endl;
    os_body << expr_to_string(b);
    os_body << std::endl << std::endl;
  }

  if(symbol.name!=ID_main &&
     symbol.name!="c::main")
  {
    os_decl << "// " << symbol.name << std::endl;
    os_decl << "// " << symbol.location << std::endl;
    os_decl << make_decl(symbol.name, symbol.type) << ";" << std::endl;
  }
}

/*******************************************************************\

Function: find_block_position_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

static bool find_block_position_rec(
  const irep_idt &identifier,
  codet &root,
  code_blockt* &dest,
  exprt::operandst::iterator &before)
{
  if(!root.has_operands())
    return false;

  code_blockt* our_dest=0;

  exprt::operandst &operands=root.operands();
  exprt::operandst::iterator first_found=operands.end();

  Forall_expr(it, operands)
  {
    bool found=false;

    // be aware of the skip-carries-type hack
    if(it->id()==ID_code &&
       to_code(*it).get_statement()!=ID_skip)
      found=find_block_position_rec(
        identifier,
        to_code(*it),
        our_dest,
        before);
    else
    {
      find_symbols_sett syms;
      find_type_and_expr_symbols(*it, syms);

      found=syms.find(identifier)!=syms.end();
    }

    if(!found) continue;

    if(!our_dest)
    {
      // first containing block
      if(root.get_statement()==ID_block)
      {
        dest=&(to_code_block(root));
        before=it;
      }

      return true;
    }
    else
    {
      // there is a containing block and this is the first operand
      // that contains identifier
      if(first_found==operands.end())
        first_found=it;
      // we have seen it already - pick the first occurrence in this
      // block
      else if(root.get_statement()==ID_block)
      {
        dest=&(to_code_block(root));
        before=first_found;

        return true;
      }
      // we have seen it already - outer block has to deal with this
      else
        return true;
    }
  }

  if(first_found!=operands.end())
  {
    dest=our_dest;

    return true;
  }

  return false;
}

/*******************************************************************\

Function: dump_ct::insert_local_static_decls

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::insert_local_static_decls(
  code_blockt &b,
  const std::list<irep_idt> &local_static,
  local_static_declst &local_static_decls,
  std::list<irep_idt> &type_decls,
  const hash_map_cont<irep_idt, irep_idt, irep_id_hash> &original_tags)
{
  // look up last identifier first as its value may introduce the
  // other ones
  for(std::list<irep_idt>::const_reverse_iterator
      it=local_static.rbegin();
      it!=local_static.rend();
      ++it)
  {
    local_static_declst::const_iterator d_it=
      local_static_decls.find(*it);
    assert(d_it!=local_static_decls.end());

    code_declt d=d_it->second;
    std::list<irep_idt> redundant;
    cleanup_decl(d, redundant, type_decls, original_tags);

    code_blockt* dest_ptr=0;
    exprt::operandst::iterator before=b.operands().end();

    // some use of static variables might be optimised out if it is
    // within an if(false) { ... } block
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      assert(dest_ptr!=0);
      dest_ptr->operands().insert(before, d);
    }
  }
}

/*******************************************************************\

Function: dump_ct::insert_local_type_decls

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::insert_local_type_decls(
  code_blockt &b,
  const std::list<irep_idt> &type_decls)
{
  // look up last identifier first as its value may introduce the
  // other ones
  for(std::list<irep_idt>::const_reverse_iterator
      it=type_decls.rbegin();
      it!=type_decls.rend();
      ++it)
  {
    const typet &type=ns.lookup(*it).type;
    // feed through plain C to expr2c by ending and re-starting
    // a comment block ...
    std::ostringstream os_body;
    os_body << *it << " */\n";
    convert_compound(type, false, os_body);
    os_body << "/*";

    code_skipt skip;
    skip.add_source_location().set_comment(os_body.str());
    // another hack to ensure symbols inside types are seen
    skip.type()=type;

    code_blockt* dest_ptr=0;
    exprt::operandst::iterator before=b.operands().end();

    // we might not find it in case a transparent union type cast
    // has been removed by cleanup operations
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      assert(dest_ptr!=0);
      dest_ptr->operands().insert(before, skip);
    }
  }
}

/*******************************************************************\

Function: dump_ct::cleanup_expr

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::cleanup_expr(exprt &expr)
{
  Forall_operands(it, expr)
    cleanup_expr(*it);

  cleanup_type(expr.type());

  if(expr.id()==ID_struct)
  {
    struct_typet type=
      to_struct_type(ns.follow(expr.type()));

    struct_union_typet::componentst old_components;
    old_components.swap(type.components());

    exprt::operandst old_ops;
    old_ops.swap(expr.operands());

    assert(old_components.size()==old_ops.size());
    exprt::operandst::iterator o_it=old_ops.begin();
    for(struct_union_typet::componentst::const_iterator
        it=old_components.begin();
        it!=old_components.end();
        ++it)
    {
      const typet &comp_type=ns.follow(it->type());

      const bool is_zero_bit_field=
        it->get_is_bit_field() &&
        ((comp_type.id()!=ID_c_enum &&
          to_bitvector_type(comp_type).get_width()==0) ||
         (comp_type.id()==ID_c_enum &&
          to_bitvector_type(comp_type.subtype()).get_width()==0));

      if(!it->get_is_padding() && !is_zero_bit_field)
      {
        type.components().push_back(*it);
        expr.move_to_operands(*o_it);
      }
      ++o_it;
    }
    expr.type().swap(type);
  }
  else if(expr.id()==ID_union &&
          (expr.type().get_bool(ID_C_transparent_union) ||
           ns.follow(expr.type()).get_bool(ID_C_transparent_union)))
  {
    union_exprt &u=to_union_expr(expr);

    // add a typecast for NULL
    if(u.op().id()==ID_constant &&
       u.op().type().id()==ID_pointer &&
       u.op().type().subtype().id()==ID_empty &&
       (u.op().is_zero() || to_constant_expr(u.op()).get_value()==ID_NULL))
    {
      const struct_union_typet::componentt &comp=
        to_union_type(ns.follow(u.type())).get_component(u.get_component_name());
      const typet &u_op_type=comp.type();
      assert(u_op_type.id()==ID_pointer);

      typecast_exprt tc(u.op(), u_op_type);
      expr.swap(tc);
    }
    else
    {
      exprt tmp;
      tmp.swap(u.op());
      expr.swap(tmp);
    }
  }
  else if(expr.id()==ID_typecast &&
      expr.op0().id()==ID_typecast &&
      base_type_eq(expr.type(), expr.op0().type(), ns))
  {
    exprt tmp=expr.op0();
    expr.swap(tmp);
  }
  else if(expr.id()==ID_code &&
          to_code(expr).get_statement()==ID_function_call &&
          to_code_function_call(to_code(expr)).function().id()==ID_symbol)
  {
    code_function_callt &call=to_code_function_call(to_code(expr));
    const symbol_exprt &fn=to_symbol_expr(call.function());
    code_function_callt::argumentst &arguments=call.arguments();

    // don't edit function calls we might have introduced
    if(has_prefix(id2string(fn.get_identifier()), "c::"))
    {
      const symbolt &fn_sym=ns.lookup(fn.get_identifier());
      const code_typet &code_type=to_code_type(fn_sym.type);
      const code_typet::parameterst &parameters=code_type.parameters();

      if(parameters.size()==arguments.size())
      {
        code_typet::parameterst::const_iterator it=parameters.begin();
        Forall_expr(it2, arguments)
        {
          const typet &type=ns.follow(it->type());
          if(type.id()==ID_union &&
             type.get_bool(ID_C_transparent_union))
          {
            if(it2->id()==ID_typecast &&
               base_type_eq(it2->type(), type, ns))
              *it2=to_typecast_expr(*it2).op();

            // add a typecast for NULL or 0
            if(it2->id()==ID_constant &&
               (it2->is_zero() || to_constant_expr(*it2).get_value()==ID_NULL))
            {
              const typet &comp_type=
                to_union_type(type).components().front().type();

              if(comp_type.id()==ID_pointer)
                *it2=typecast_exprt(*it2, comp_type);
            }
          }

          ++it;
        }
      }
    }
  }
}

/*******************************************************************\

Function: dump_ct::cleanup_type

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void dump_ct::cleanup_type(typet &type)
{
  Forall_subtypes(it, type)
    cleanup_type(*it);

  if(type.id()==ID_array)
    cleanup_expr(to_array_type(type).size());

  assert((type.id()!=ID_union && type.id()!=ID_struct) ||
         !type.get(ID_tag).empty());
}

/*******************************************************************\

Function: dump_ct::type_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string dump_ct::type_to_string(const typet &type)
{
  std::string ret;
  typet t=type;
  cleanup_type(t);
  language->from_type(t, ret, ns);
  return ret;

#if 0
  if(type.id()==ID_bool)
    #if 0
    ret="bool";
    #else
    ret="_Bool";
    #endif
  else if(type.id()==ID_signedbv)
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
  else if(type.id()==ID_verilogbv)
  {
    return "__verilogbv<"+id2string(type.get(ID_width))+"> ";
  }
#endif
}

/*******************************************************************\

Function: dump_ct::expr_to_string

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::string dump_ct::expr_to_string(const exprt &expr)
{
  std::string ret;
  exprt e=expr;
  cleanup_expr(e);
  language->from_expr(e, ret, ns);
  return ret;

#if 0
  else if(expr.id()==ID_constant)
  {
    if(expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_unsignedbv)
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

    if(expr.type().id()==ID_bool)
      return expr.is_true()?"1":"0";

    if(expr.type().id()==ID_pointer)
    {
      assert(expr.get(ID_value)==ID_NULL);
      return "0";
    }

    if(expr.type().id()==ID_verilogbv)
    {
      if(expr.type().get(ID_width)=="1")
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

    #if 0
    if(expr.type().id()==ID_c_enum)
    {
      std::string str = "__signedbv<" + id2string(expr.type().get(ID_width)) +
        "> (" + id2string(expr.get(ID_value)) + ")";
      return str;
    }
    #endif

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

    return "__" + id2string(expr.type().id())
           + "<"+ id2string(expr.type().get(ID_width)) + "> ("
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
  else if(expr.id()==ID_side_effect)
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
    std::string get_value = expr.get_string(ID_value);
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
        id2string(global_renaming[expr.get(ID_component_name)]);

      std::string type =
        id2string(global_renaming[t.get(ID_name)]);

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

    std::string ret=id2string(global_renaming[struct_type.get(ID_name)])+"(";
    
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
#endif
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
  dump_ct goto2c(src, ns, new_ansi_c_language);
  out << goto2c;
}

/*******************************************************************\

Function: dump_cpp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_cpp(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out)
{
  dump_ct goto2cpp(src, ns, new_cpp_language);
  out << goto2cpp;
}

