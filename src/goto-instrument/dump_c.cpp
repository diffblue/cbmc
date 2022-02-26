/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dump Goto-Program as C/C++ Source

#include "dump_c.h"
#include "dump_c_class.h"

#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/get_base_name.h>
#include <util/invariant.h>
#include <util/replace_symbol.h>
#include <util/string_utils.h>

#include <ansi-c/expr2c.h>
#include <cpp/expr2cpp.h>
#include <linking/static_lifetime_init.h>

#include "goto_program2code.h"

dump_c_configurationt dump_c_configurationt::default_configuration =
  dump_c_configurationt();

dump_c_configurationt dump_c_configurationt::type_header_configuration =
  dump_c_configurationt()
    .disable_include_function_decls()
    .disable_include_function_bodies()
    .disable_include_global_vars()
    .enable_include_headers();

inline std::ostream &operator << (std::ostream &out, dump_ct &src)
{
  src(out);
  return out;
}

void dump_ct::operator()(std::ostream &os)
{
  std::stringstream func_decl_stream;
  std::stringstream compound_body_stream;
  std::stringstream global_var_stream;
  std::stringstream global_decl_stream;
  std::stringstream global_decl_header_stream;
  std::stringstream func_body_stream;
  local_static_declst local_static_decls;

  // add copies of struct types when ID_C_transparent_union is only
  // annotated to parameter
  symbol_tablet symbols_transparent;
  for(const auto &named_symbol : copied_symbol_table.symbols)
  {
    const symbolt &symbol=named_symbol.second;

    if(symbol.type.id()!=ID_code)
      continue;

    code_typet &code_type=to_code_type(
      copied_symbol_table.get_writeable_ref(named_symbol.first).type);
    code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::iterator
        it2=parameters.begin();
        it2!=parameters.end();
        ++it2)
    {
      typet &type=it2->type();

      if(type.id() == ID_union_tag && type.get_bool(ID_C_transparent_union))
      {
        symbolt new_type_sym =
          ns.lookup(to_union_tag_type(type).get_identifier());

        new_type_sym.name=id2string(new_type_sym.name)+"$transparent";
        new_type_sym.type.set(ID_C_transparent_union, true);

        // we might have it already, in which case this has no effect
        symbols_transparent.add(new_type_sym);

        to_union_tag_type(type).set_identifier(new_type_sym.name);
        type.remove(ID_C_transparent_union);
      }
    }
  }
  for(const auto &symbol_pair : symbols_transparent.symbols)
  {
    copied_symbol_table.add(symbol_pair.second);
  }

  typedef std::unordered_map<irep_idt, unsigned> unique_tagst;
  unique_tagst unique_tags;

  // add tags to anonymous union/struct/enum,
  // and prepare lexicographic order
  std::set<std::string> symbols_sorted;
  for(const auto &named_symbol : copied_symbol_table.symbols)
  {
    symbolt &symbol = copied_symbol_table.get_writeable_ref(named_symbol.first);
    bool tag_added=false;

    // TODO we could get rid of some of the ID_anonymous by looking up
    // the origin symbol types in typedef_types and adjusting any other
    // uses of ID_tag
    if((symbol.type.id()==ID_union || symbol.type.id()==ID_struct) &&
       symbol.type.get(ID_tag).empty())
    {
      PRECONDITION(symbol.is_type);
      symbol.type.set(ID_tag, ID_anonymous);
      tag_added=true;
    }
    else if(symbol.type.id()==ID_c_enum &&
            symbol.type.find(ID_tag).get(ID_C_base_name).empty())
    {
      PRECONDITION(symbol.is_type);
      symbol.type.add(ID_tag).set(ID_C_base_name, ID_anonymous);
      tag_added=true;
    }

    const std::string name_str=id2string(named_symbol.first);
    if(symbol.is_type &&
       (symbol.type.id()==ID_union ||
        symbol.type.id()==ID_struct ||
        symbol.type.id()==ID_c_enum))
    {
      std::string new_tag=symbol.type.id()==ID_c_enum?
        symbol.type.find(ID_tag).get_string(ID_C_base_name):
        symbol.type.get_string(ID_tag);

      std::string::size_type tag_pos=new_tag.rfind("tag-");
      if(tag_pos!=std::string::npos)
        new_tag.erase(0, tag_pos+4);
      const std::string new_tag_base=new_tag;

      for(std::pair<unique_tagst::iterator, bool>
          unique_entry=unique_tags.insert(std::make_pair(new_tag, 0));
          !unique_entry.second;
          unique_entry=unique_tags.insert(std::make_pair(new_tag, 0)))
      {
        new_tag=new_tag_base+"$"+
          std::to_string(unique_entry.first->second);
        ++(unique_entry.first->second);
      }

      if(symbol.type.id()==ID_c_enum)
      {
        symbol.type.add(ID_tag).set(ID_C_base_name, new_tag);
        symbol.base_name=new_tag;
      }
      else
        symbol.type.set(ID_tag, new_tag);
    }

    // we don't want to dump in full all definitions; in particular
    // do not dump anonymous types that are defined in system headers
    if((!tag_added || symbol.is_type) &&
       system_symbols.is_symbol_internal_symbol(symbol, system_headers) &&
       symbol.name!=goto_functions.entry_point())
      continue;

    bool inserted=symbols_sorted.insert(name_str).second;
    CHECK_RETURN(inserted);
  }

  gather_global_typedefs();

  // collect all declarations we might need, include local static variables
  bool skip_function_main=false;
  std::vector<std::string> header_files;
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);
    const irep_idt &type_id=symbol.type.id();

    if(symbol.is_type &&
       symbol.location.get_function().empty() &&
       (type_id==ID_struct ||
        type_id==ID_union ||
        type_id==ID_c_enum))
    {
      if(!system_symbols.is_symbol_internal_symbol(symbol, system_headers))
      {
        global_decl_stream << "// " << symbol.name << '\n';
        global_decl_stream << "// " << symbol.location << '\n';

        std::string location_file =
          get_base_name(id2string(symbol.location.get_file()), false);
        // collect header the types are borrowed from
        // expect header files to end in .h
        if(
          location_file.length() > 1 &&
          location_file[location_file.length() - 1] == 'h')
        {
          std::vector<std::string>::iterator it =
            find(header_files.begin(), header_files.end(), location_file);
          if(it == header_files.end())
          {
            header_files.push_back(location_file);
            global_decl_header_stream << "#include \"" << location_file
                                      << "\"\n";
          }
        }

        if(type_id==ID_c_enum)
          convert_compound_enum(symbol.type, global_decl_stream);
        else if(type_id == ID_struct)
        {
          global_decl_stream << type_to_string(struct_tag_typet{symbol.name})
                             << ";\n\n";
        }
        else
        {
          global_decl_stream << type_to_string(union_tag_typet{symbol.name})
                             << ";\n\n";
        }
      }
    }
    else if(
      symbol.is_static_lifetime && symbol.type.id() != ID_code &&
      !symbol.type.get_bool(ID_C_do_not_dump))
      convert_global_variable(
          symbol,
          global_var_stream,
          local_static_decls);
    else if(symbol.type.id()==ID_code)
    {
      goto_functionst::function_mapt::const_iterator func_entry=
        goto_functions.function_map.find(symbol.name);

      if(
        !harness && func_entry != goto_functions.function_map.end() &&
        func_entry->second.body_available() &&
        (symbol.name == ID_main ||
         (config.main.has_value() && symbol.name == config.main.value())))
      {
        skip_function_main=true;
      }
    }
  }

  // function declarations and definitions
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(symbol.type.id()!=ID_code ||
       symbol.is_type)
      continue;

    convert_function_declaration(
      symbol,
      skip_function_main,
      func_decl_stream,
      func_body_stream,
      local_static_decls);
  }

  // (possibly modified) compound types
  for(std::set<std::string>::const_iterator
      it=symbols_sorted.begin();
      it!=symbols_sorted.end();
      ++it)
  {
    const symbolt &symbol=ns.lookup(*it);

    if(
      symbol.is_type &&
      (symbol.type.id() == ID_struct || symbol.type.id() == ID_union))
      convert_compound_declaration(
          symbol,
          compound_body_stream);
  }

  // Dump the code to the target stream;
  // the statements before to this point collect the code to dump!
  for(std::set<std::string>::const_iterator
      it=system_headers.begin();
      it!=system_headers.end();
      ++it)
    os << "#include <" << *it << ">\n";
  if(!system_headers.empty())
    os << '\n';

  if(!global_decl_header_stream.str().empty() && dump_c_config.include_headers)
    os << global_decl_header_stream.str() << '\n';

  if(global_var_stream.str().find("NULL")!=std::string::npos ||
     func_body_stream.str().find("NULL")!=std::string::npos)
  {
    os << "#ifndef NULL\n"
       << "#define NULL ((void*)0)\n"
       << "#endif\n\n";
  }
  if(func_body_stream.str().find("FENCE")!=std::string::npos)
  {
    os << "#ifndef FENCE\n"
       << "#define FENCE(x) ((void)0)\n"
       << "#endif\n\n";
  }
  if(func_body_stream.str().find("IEEE_FLOAT_")!=std::string::npos)
  {
    os << "#ifndef IEEE_FLOAT_EQUAL\n"
       << "#define IEEE_FLOAT_EQUAL(x,y) ((x)==(y))\n"
       << "#endif\n"
       << "#ifndef IEEE_FLOAT_NOTEQUAL\n"
       << "#define IEEE_FLOAT_NOTEQUAL(x,y) ((x)!=(y))\n"
       << "#endif\n\n";
  }

  if(!global_decl_stream.str().empty() && dump_c_config.include_global_decls)
    os << global_decl_stream.str() << '\n';

  if(dump_c_config.include_typedefs)
    dump_typedefs(os);

  if(!func_decl_stream.str().empty() && dump_c_config.include_function_decls)
    os << func_decl_stream.str() << '\n';
  if(!compound_body_stream.str().empty() && dump_c_config.include_compounds)
    os << compound_body_stream.str() << '\n';
  if(!global_var_stream.str().empty() && dump_c_config.include_global_vars)
    os << global_var_stream.str() << '\n';
  if(dump_c_config.include_function_bodies)
    os << func_body_stream.str();
}

/// declare compound types
void dump_ct::convert_compound_declaration(
    const symbolt &symbol,
    std::ostream &os_body)
{
  if(
    !symbol.location.get_function().empty() ||
    symbol.type.get_bool(ID_C_do_not_dump))
  {
    return;
  }

  // do compound type body
  if(symbol.type.id() == ID_struct)
    convert_compound(
      symbol.type,
      struct_tag_typet(symbol.name),
      dump_c_config.follow_compounds,
      os_body);
  else if(symbol.type.id() == ID_union)
    convert_compound(
      symbol.type,
      union_tag_typet(symbol.name),
      dump_c_config.follow_compounds,
      os_body);
  else if(symbol.type.id() == ID_c_enum)
    convert_compound(
      symbol.type,
      c_enum_tag_typet(symbol.name),
      dump_c_config.follow_compounds,
      os_body);
}

void dump_ct::convert_compound(
  const typet &type,
  const typet &unresolved,
  bool recursive,
  std::ostream &os)
{
  if(
    type.id() == ID_c_enum_tag || type.id() == ID_struct_tag ||
    type.id() == ID_union_tag)
  {
    const symbolt &symbol = ns.lookup(to_tag_type(type));
    DATA_INVARIANT(symbol.is_type, "tag expected to be type symbol");

    if(!system_symbols.is_symbol_internal_symbol(symbol, system_headers))
      convert_compound(symbol.type, unresolved, recursive, os);
  }
  else if(type.id()==ID_array || type.id()==ID_pointer)
  {
    if(!recursive)
      return;

    convert_compound(
      to_type_with_subtype(type).subtype(),
      to_type_with_subtype(type).subtype(),
      recursive,
      os);

    // sizeof may contain a type symbol that has to be declared first
    if(type.id()==ID_array)
    {
      find_symbols_sett syms;
      find_non_pointer_type_symbols(to_array_type(type).size(), syms);

      for(find_symbols_sett::const_iterator
          it=syms.begin();
          it!=syms.end();
          ++it)
      {
        const symbolt &type_symbol = ns.lookup(*it);
        irep_idt tag_kind =
          type_symbol.type.id() == ID_c_enum
            ? ID_c_enum_tag
            : (type_symbol.type.id() == ID_union ? ID_union_tag
                                                 : ID_struct_tag);
        tag_typet s_type(tag_kind, *it);
        convert_compound(s_type, s_type, recursive, os);
      }
    }
  }
  else if(type.id()==ID_struct || type.id()==ID_union)
    convert_compound(to_struct_union_type(type), unresolved, recursive, os);
  else if(type.id()==ID_c_enum)
    convert_compound_enum(type, os);
}

void dump_ct::convert_compound(
  const struct_union_typet &type,
  const typet &unresolved,
  bool recursive,
  std::ostream &os)
{
  const irep_idt &name=type.get(ID_tag);

  if(!converted_compound.insert(name).second || type.get_bool(ID_C_do_not_dump))
    return;

  // make sure typedef names used in the declaration are available
  collect_typedefs(type, true);

  const irept &bases = type.find(ID_bases);
  std::stringstream base_decls;
  for(const auto &parent : bases.get_sub())
  {
    UNREACHABLE;
    (void)parent;
#if 0
    assert(parent.id() == ID_base);
    assert(parent.get(ID_type) == ID_struct_tag);

    const irep_idt &base_id=
      parent.find(ID_type).get(ID_identifier);
    const irep_idt &renamed_base_id=global_renaming[base_id];
    const symbolt &parsymb=ns.lookup(renamed_base_id);

    convert_compound_rec(parsymb.type, os);

    base_decls << id2string(renamed_base_id) +
      (parent_it+1==bases.get_sub().end()?"":", ");
#endif
  }

#if 0
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
#endif

  std::stringstream struct_body;

  for(const auto &comp : type.components())
  {
    const typet &comp_type = comp.type();

    if(comp_type.id()==ID_code ||
       comp.get_bool(ID_from_base) ||
       comp.get_is_padding())
      continue;

    const typet *non_array_type = &comp_type;
    while(non_array_type->id()==ID_array)
      non_array_type = &(to_array_type(*non_array_type).element_type());

    if(recursive)
    {
      if(non_array_type->id()!=ID_pointer)
        convert_compound(comp.type(), comp.type(), recursive, os);
      else
        collect_typedefs(comp.type(), true);
    }

    irep_idt comp_name=comp.get_name();

    struct_body << indent(1) << "// " << comp_name << '\n';
    struct_body << indent(1);

    // component names such as "main" would collide with other objects in the
    // namespace
    std::string fake_unique_name="NO/SUCH/NS::"+id2string(comp_name);
    std::string s=make_decl(fake_unique_name, comp.type());
    POSTCONDITION(s.find("NO/SUCH/NS")==std::string::npos);

    if(comp_type.id()==ID_c_bit_field &&
       to_c_bit_field_type(comp_type).get_width()==0)
    {
      comp_name.clear();
      s=type_to_string(comp_type);
    }

    if(s.find(CPROVER_PREFIX "bitvector") == std::string::npos)
    {
      struct_body << s;
    }
    else if(comp_type.id()==ID_signedbv)
    {
      const signedbv_typet &t=to_signedbv_type(comp_type);
      if(t.get_width()<=config.ansi_c.long_long_int_width)
        struct_body << "long long int " << comp_name
          << " : " << t.get_width();
      else if(mode == ID_cpp)
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
      else if(mode == ID_cpp)
        struct_body << "__unsignedbv<" << t.get_width() << "> "
          << comp_name;
      else
        struct_body << s;
    }
    else
      UNREACHABLE;

    struct_body << ";\n";
  }

  typet unresolved_clean=unresolved;
  irep_idt typedef_str;
  for(auto td_entry : typedef_types)
  {
    if(
      td_entry.first.get(ID_identifier) == unresolved.get(ID_identifier) &&
      (td_entry.first.source_location() == unresolved.source_location()))
    {
      unresolved_clean.remove(ID_C_typedef);
      typedef_str = td_entry.second;
      std::pair<typedef_mapt::iterator, bool> td_map_entry =
        typedef_map.insert({typedef_str, typedef_infot(typedef_str)});
      PRECONDITION(!td_map_entry.second);
      if(!td_map_entry.first->second.early)
        td_map_entry.first->second.type_decl_str.clear();
      os << "typedef ";
      break;
    }
  }

  os << type_to_string(unresolved_clean);
  if(!base_decls.str().empty())
  {
    PRECONDITION(mode == ID_cpp);
    os << ": " << base_decls.str();
  }
  os << '\n';
  os << "{\n";
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
  if(!typedef_str.empty())
    os << " " << typedef_str;
  os << ";\n\n";
}

void dump_ct::convert_compound_enum(
  const typet &type,
  std::ostream &os)
{
  PRECONDITION(type.id()==ID_c_enum);

  const irept &tag=type.find(ID_tag);
  const irep_idt &name=tag.get(ID_C_base_name);

  if(tag.is_nil() ||
     !converted_enum.insert(name).second)
    return;

  c_enum_typet enum_type=to_c_enum_type(type);
  c_enum_typet::memberst &members=
    (c_enum_typet::memberst &)(enum_type.add(ID_body).get_sub());
  for(c_enum_typet::memberst::iterator
      it=members.begin();
      it!=members.end();
      ++it)
  {
    const irep_idt bn=it->get_base_name();

    if(declared_enum_constants.find(bn)!=
       declared_enum_constants.end() ||
       copied_symbol_table.has_symbol(bn))
    {
      std::string new_bn=id2string(name)+"$$"+id2string(bn);
      it->set_base_name(new_bn);
    }

    declared_enum_constants.insert(
      std::make_pair(bn, it->get_base_name()));
  }

  os << type_to_string(enum_type);

  if(enum_type.get_bool(ID_C_packed))
    os << " __attribute__ ((__packed__))";

  os << ";\n\n";
}

void dump_ct::cleanup_decl(
  code_frontend_declt &decl,
  std::list<irep_idt> &local_static,
  std::list<irep_idt> &local_type_decls)
{
  goto_programt tmp;
  tmp.add(goto_programt::make_decl(decl.symbol()));

  if(optionalt<exprt> value = decl.initial_value())
  {
    decl.set_initial_value({});
    tmp.add(goto_programt::make_assignment(decl.symbol(), std::move(*value)));
  }

  tmp.add(goto_programt::make_end_function());

  // goto_program2codet requires valid location numbers:
  tmp.update();

  std::unordered_set<irep_idt> typedef_names;
  for(const auto &td : typedef_map)
    typedef_names.insert(td.first);

  code_blockt b;
  goto_program2codet p2s(
    irep_idt(),
    tmp,
    copied_symbol_table,
    b,
    local_static,
    local_type_decls,
    typedef_names,
    system_headers);
  p2s();

  POSTCONDITION(b.statements().size() == 1);
  decl.swap(b.op0());
}

/// Find any typedef names contained in the input type and store their
/// declaration strings in typedef_map for eventual output.
/// \param type: type to inspect for ID_C_typedef entry
/// \param early: set to true to enforce that typedef is dumped before any
///   function declarations or struct definitions
void dump_ct::collect_typedefs(const typet &type, bool early)
{
  std::unordered_set<irep_idt> deps;
  collect_typedefs_rec(type, early, deps);
}

/// Find any typedef names contained in the input type and store their
/// declaration strings in typedef_map for eventual output.
/// \param type: type to inspect for ID_C_typedef entry
/// \param early: set to true to enforce that typedef is dumped before any
///   function declarations or struct definitions
/// \param [out] dependencies: typedefs used in the declaration of a given
///   typedef
void dump_ct::collect_typedefs_rec(
  const typet &type,
  bool early,
  std::unordered_set<irep_idt> &dependencies)
{
  if(system_symbols.is_type_internal(type, system_headers))
    return;

  std::unordered_set<irep_idt> local_deps;

  if(type.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(type);

    collect_typedefs_rec(code_type.return_type(), early, local_deps);
    for(const auto &param : code_type.parameters())
      collect_typedefs_rec(param.type(), early, local_deps);
  }
  else if(type.id()==ID_pointer || type.id()==ID_array)
  {
    collect_typedefs_rec(
      to_type_with_subtype(type).subtype(), early, local_deps);
  }
  else if(
    type.id() == ID_c_enum_tag || type.id() == ID_struct_tag ||
    type.id() == ID_union_tag)
  {
    const symbolt &symbol = ns.lookup(to_tag_type(type));
    collect_typedefs_rec(symbol.type, early, local_deps);
  }

  const irep_idt &typedef_str=type.get(ID_C_typedef);

  if(!typedef_str.empty())
  {
    std::pair<typedef_mapt::iterator, bool> entry=
      typedef_map.insert({typedef_str, typedef_infot(typedef_str)});

    if(entry.second ||
       (early && entry.first->second.type_decl_str.empty()))
    {
      if(typedef_str=="__gnuc_va_list" || typedef_str == "va_list")
      {
        system_headers.insert("stdarg.h");
        early=false;
      }
      else
      {
        typet t=type;
        t.remove(ID_C_typedef);

        std::ostringstream oss;
        oss << "typedef " << make_decl(typedef_str, t) << ';';

        entry.first->second.type_decl_str=oss.str();
        entry.first->second.dependencies=local_deps;
      }
    }

    if(early)
    {
      entry.first->second.early=true;

      for(const auto &d : local_deps)
      {
        auto td_entry=typedef_map.find(d);
        PRECONDITION(td_entry!=typedef_map.end());
        td_entry->second.early=true;
      }
    }

    dependencies.insert(typedef_str);
  }

  dependencies.insert(local_deps.begin(), local_deps.end());
}

/// Find all global typdefs in the symbol table and store them in typedef_types
void dump_ct::gather_global_typedefs()
{
  // sort the symbols first to ensure deterministic replacement in
  // typedef_types below as there could be redundant declarations
  // typedef int x;
  // typedef int y;
  std::map<std::string, symbolt> symbols_sorted;
  for(const auto &symbol_entry : copied_symbol_table.symbols)
    symbols_sorted.insert(
      {id2string(symbol_entry.first), symbol_entry.second});

  for(const auto &symbol_entry : symbols_sorted)
  {
    const symbolt &symbol=symbol_entry.second;

    if(symbol.is_macro && symbol.is_type &&
       symbol.location.get_function().empty())
    {
      const irep_idt &typedef_str=symbol.type.get(ID_C_typedef);
      PRECONDITION(!typedef_str.empty());
      typedef_types[symbol.type]=typedef_str;
      if(system_symbols.is_symbol_internal_symbol(symbol, system_headers))
        typedef_map.insert({typedef_str, typedef_infot(typedef_str)});
      else
        collect_typedefs(symbol.type, false);
    }
  }
}

/// Print all typedefs that are not covered via typedef struct xyz { ... } name;
/// \param [out] os: output stream
void dump_ct::dump_typedefs(std::ostream &os) const
{
  // we need to compute a topological sort; we do so by picking all
  // typedefs the dependencies of which have been emitted into to_insert
  std::vector<typedef_infot> typedefs_sorted;
  typedefs_sorted.reserve(typedef_map.size());

  // elements in to_insert are lexicographically sorted and ready for
  // output
  std::map<std::string, typedef_infot> to_insert;

  std::unordered_set<irep_idt> typedefs_done;
  std::unordered_map<irep_idt, std::unordered_set<irep_idt>> forward_deps,
    reverse_deps;

  for(const auto &td : typedef_map)
    if(!td.second.type_decl_str.empty())
    {
      if(td.second.dependencies.empty())
        // those can be dumped immediately
        to_insert.insert({id2string(td.first), td.second});
      else
      {
        // delay them until dependencies are dumped
        forward_deps.insert({td.first, td.second.dependencies});
        for(const auto &d : td.second.dependencies)
          reverse_deps[d].insert(td.first);
      }
    }

  while(!to_insert.empty())
  {
    // the topologically next element (lexicographically ranked first
    // among all the dependencies of which have been dumped)
    typedef_infot t=to_insert.begin()->second;
    to_insert.erase(to_insert.begin());
    // move to the output queue
    typedefs_sorted.push_back(t);

    // find any depending typedefs that are now valid, or at least
    // reduce the remaining dependencies
    auto r_it=reverse_deps.find(t.typedef_name);
    if(r_it==reverse_deps.end())
      continue;

    // reduce remaining dependencies
    std::unordered_set<irep_idt> &r_deps = r_it->second;
    for(std::unordered_set<irep_idt>::iterator it = r_deps.begin();
        it != r_deps.end();) // no ++it
    {
      auto f_it=forward_deps.find(*it);
      if(f_it==forward_deps.end()) // might be done already
      {
        it=r_deps.erase(it);
        continue;
      }

      // update dependencies
      std::unordered_set<irep_idt> &f_deps = f_it->second;
      PRECONDITION(!f_deps.empty());
      PRECONDITION(f_deps.find(t.typedef_name)!=f_deps.end());
      f_deps.erase(t.typedef_name);

      if(f_deps.empty()) // all depenencies done now!
      {
        const auto td_entry=typedef_map.find(*it);
        PRECONDITION(td_entry!=typedef_map.end());
        to_insert.insert({id2string(*it), td_entry->second});
        forward_deps.erase(*it);
        it=r_deps.erase(it);
      }
      else
        ++it;
    }
  }

  POSTCONDITION(forward_deps.empty());

  for(const auto &td : typedefs_sorted)
    os << td.type_decl_str << '\n';

  if(!typedefs_sorted.empty())
    os << '\n';
}

void dump_ct::convert_global_variable(
    const symbolt &symbol,
    std::ostream &os,
    local_static_declst &local_static_decls)
{
  const irep_idt &func=symbol.location.get_function();
  if((func.empty() || symbol.is_extern || symbol.value.is_not_nil()) &&
      !converted_global.insert(symbol.name).second)
    return;

  code_frontend_declt d(symbol.symbol_expr());

  find_symbols_sett syms;
  if(symbol.value.is_not_nil())
    find_symbols_or_nexts(symbol.value, syms);

  // add a tentative declaration to cater for symbols in the initializer
  // relying on it this symbol
  if((func.empty() || symbol.is_extern) &&
     (symbol.value.is_nil() || !syms.empty()))
  {
    os << "// " << symbol.name << '\n';
    os << "// " << symbol.location << '\n';
    os << expr_to_string(d) << '\n';
  }

  if(!symbol.value.is_nil())
  {
    std::set<std::string> symbols_sorted;
    for(find_symbols_sett::const_iterator
        it=syms.begin();
        it!=syms.end();
        ++it)
    {
      bool inserted=symbols_sorted.insert(id2string(*it)).second;
      CHECK_RETURN(inserted);
    }

    for(std::set<std::string>::const_iterator
        it=symbols_sorted.begin();
        it!=symbols_sorted.end();
        ++it)
    {
      const symbolt &sym=ns.lookup(*it);
      if(!sym.is_type && sym.is_static_lifetime && sym.type.id()!=ID_code)
        convert_global_variable(sym, os, local_static_decls);
    }

    d.copy_to_operands(symbol.value);
  }

  if(!func.empty() && !symbol.is_extern)
  {
    local_static_decls.emplace(symbol.name, d);
  }
  else if(!symbol.value.is_nil())
  {
    os << "// " << symbol.name << '\n';
    os << "// " << symbol.location << '\n';

    std::list<irep_idt> empty_static, empty_types;
    cleanup_decl(d, empty_static, empty_types);
    CHECK_RETURN(empty_static.empty());
    os << expr_to_string(d) << '\n';
  }
}

/// Replace CPROVER internal symbols in b by printable values and generate
/// necessary declarations.
/// \param b: Code block to be cleaned
void dump_ct::cleanup_harness(code_blockt &b)
{
  replace_symbolt replace;
  code_blockt decls;

  const symbolt *argc_sym=nullptr;
  if(!ns.lookup("argc'", argc_sym))
  {
    symbol_exprt argc("argc", argc_sym->type);
    replace.insert(argc_sym->symbol_expr(), argc);
    code_declt d(argc);
    decls.add(d);
  }
  const symbolt *argv_sym=nullptr;
  if(!ns.lookup("argv'", argv_sym))
  {
    symbol_exprt argv("argv", argv_sym->type);
    // replace argc' by argc in the type of argv['] to maintain type consistency
    // while replacing
    replace(argv);
    replace.insert(symbol_exprt(argv_sym->name, argv.type()), argv);
    code_declt d(argv);
    decls.add(d);
  }
  const symbolt *return_sym=nullptr;
  if(!ns.lookup("return'", return_sym))
  {
    symbol_exprt return_value("return_value", return_sym->type);
    replace.insert(return_sym->symbol_expr(), return_value);
    code_declt d(return_value);
    decls.add(d);
  }

  for(auto &code : b.statements())
  {
    if(code.get_statement()==ID_function_call)
    {
      exprt &func=to_code_function_call(code).function();
      if(func.id()==ID_symbol)
      {
        symbol_exprt &s=to_symbol_expr(func);
        if(s.get_identifier()==ID_main)
          s.set_identifier(CPROVER_PREFIX+id2string(ID_main));
        else if(s.get_identifier() == INITIALIZE_FUNCTION)
          continue;
      }
    }

    decls.add(code);
  }

  b.swap(decls);
  replace(b);
}

void dump_ct::convert_function_declaration(
    const symbolt &symbol,
    const bool skip_main,
    std::ostream &os_decl,
    std::ostream &os_body,
    local_static_declst &local_static_decls)
{
  // don't dump artificial main
  if(skip_main && symbol.name==goto_functionst::entry_point())
    return;

  // convert the goto program back to code - this might change
  // the function type
  goto_functionst::function_mapt::const_iterator func_entry=
    goto_functions.function_map.find(symbol.name);
  if(func_entry!=goto_functions.function_map.end() &&
     func_entry->second.body_available())
  {
    code_blockt b;
    std::list<irep_idt> type_decls, local_static;

    std::unordered_set<irep_idt> typedef_names;
    for(const auto &td : typedef_map)
      typedef_names.insert(td.first);

    goto_program2codet p2s(
      symbol.name,
      func_entry->second.body,
      copied_symbol_table,
      b,
      local_static,
      type_decls,
      typedef_names,
      system_headers);
    p2s();

    insert_local_static_decls(
      b,
      local_static,
      local_static_decls,
      type_decls);

    convertedt converted_c_bak(converted_compound);
    convertedt converted_e_bak(converted_enum);

    declared_enum_constants_mapt
      enum_constants_bak(declared_enum_constants);

    insert_local_type_decls(
      b,
      type_decls);

    converted_enum.swap(converted_e_bak);
    converted_compound.swap(converted_c_bak);

    if(harness && symbol.name==goto_functions.entry_point())
      cleanup_harness(b);

    os_body << "// " << symbol.name << '\n';
    os_body << "// " << symbol.location << '\n';
    if(symbol.name==goto_functions.entry_point())
      os_body << make_decl(ID_main, symbol.type) << '\n';
    else if(!harness || symbol.name!=ID_main)
      os_body << make_decl(symbol.name, symbol.type) << '\n';
    else if(harness && symbol.name==ID_main)
    {
      os_body << make_decl(CPROVER_PREFIX+id2string(symbol.name), symbol.type)
              << '\n';
    }
    os_body << expr_to_string(b);
    os_body << "\n\n";

    declared_enum_constants.swap(enum_constants_bak);
  }

  if(symbol.name!=goto_functionst::entry_point() &&
     symbol.name!=ID_main)
  {
    os_decl << "// " << symbol.name << '\n';
    os_decl << "// " << symbol.location << '\n';
    os_decl << make_decl(symbol.name, symbol.type) << ";\n";
  }
  else if(harness && symbol.name==ID_main)
  {
    os_decl << "// " << symbol.name << '\n';
    os_decl << "// " << symbol.location << '\n';
    os_decl << make_decl(CPROVER_PREFIX+id2string(symbol.name), symbol.type)
            << ";\n";
  }

  // make sure typedef names used in the function declaration are
  // available
  collect_typedefs(symbol.type, true);
}

static bool find_block_position_rec(
  const irep_idt &identifier,
  codet &root,
  code_blockt* &dest,
  exprt::operandst::iterator &before)
{
  if(!root.has_operands())
    return false;

  code_blockt *our_dest=nullptr;

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

    if(!found)
      continue;

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

void dump_ct::insert_local_static_decls(
  code_blockt &b,
  const std::list<irep_idt> &local_static,
  local_static_declst &local_static_decls,
  std::list<irep_idt> &type_decls)
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
    PRECONDITION(d_it!=local_static_decls.end());

    code_frontend_declt d = d_it->second;
    std::list<irep_idt> redundant;
    cleanup_decl(d, redundant, type_decls);

    code_blockt *dest_ptr=nullptr;
    exprt::operandst::iterator before=b.operands().end();

    // some use of static variables might be optimised out if it is
    // within an if(false) { ... } block
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      CHECK_RETURN(dest_ptr!=nullptr);
      dest_ptr->operands().insert(before, d);
    }
  }
}

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
    irep_idt tag_kind =
      type.id() == ID_c_enum
        ? ID_c_enum_tag
        : (type.id() == ID_union ? ID_union_tag : ID_struct_tag);
    convert_compound(type, tag_typet(tag_kind, *it), false, os_body);
    os_body << "/*";

    code_skipt skip;
    skip.add_source_location().set_comment(os_body.str());
    // another hack to ensure symbols inside types are seen
    skip.type()=type;

    code_blockt *dest_ptr=nullptr;
    exprt::operandst::iterator before=b.operands().end();

    // we might not find it in case a transparent union type cast
    // has been removed by cleanup operations
    if(find_block_position_rec(*it, b, dest_ptr, before))
    {
      CHECK_RETURN(dest_ptr!=nullptr);
      dest_ptr->operands().insert(before, skip);
    }
  }
}

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

    PRECONDITION(old_components.size()==old_ops.size());
    exprt::operandst::iterator o_it=old_ops.begin();
    for(const auto &old_comp : old_components)
    {
      const bool is_zero_bit_field =
        old_comp.type().id() == ID_c_bit_field &&
        to_c_bit_field_type(old_comp.type()).get_width() == 0;

      if(!old_comp.get_is_padding() && !is_zero_bit_field)
      {
        type.components().push_back(old_comp);
        expr.add_to_operands(std::move(*o_it));
      }
      ++o_it;
    }
    expr.type().swap(type);
  }
  else if(expr.id()==ID_union)
  {
    union_exprt &u=to_union_expr(expr);
    const union_typet &u_type_f=to_union_type(ns.follow(u.type()));

    if(!u.type().get_bool(ID_C_transparent_union) &&
       !u_type_f.get_bool(ID_C_transparent_union))
    {
      if(u_type_f.get_component(u.get_component_name()).get_is_padding())
        // we just use an empty struct to fake an empty union
        expr = struct_exprt({}, struct_typet());
    }
    // add a typecast for NULL
    else if(
      u.op().id() == ID_constant && is_null_pointer(to_constant_expr(u.op())) &&
      u.op().type().subtype().id() == ID_empty)
    {
      const struct_union_typet::componentt &comp=
        u_type_f.get_component(u.get_component_name());
      const typet &u_op_type=comp.type();
      PRECONDITION(u_op_type.id()==ID_pointer);

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
  else if(
    expr.id() == ID_typecast &&
    to_typecast_expr(expr).op().id() == ID_typecast &&
    expr.type() == to_typecast_expr(expr).op().type())
  {
    exprt tmp = to_typecast_expr(expr).op();
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
    const symbolt *s;
    if(!ns.lookup(fn.get_identifier(), s))
    {
      const symbolt &fn_sym=ns.lookup(fn.get_identifier());
      const code_typet &code_type=to_code_type(fn_sym.type);
      const code_typet::parameterst &parameters=code_type.parameters();

      if(parameters.size()==arguments.size())
      {
        code_typet::parameterst::const_iterator it=parameters.begin();
        for(auto &argument : arguments)
        {
          const typet &type=ns.follow(it->type());
          if(type.id()==ID_union &&
             type.get_bool(ID_C_transparent_union))
          {
            if(argument.id() == ID_typecast && argument.type() == type)
              argument = to_typecast_expr(argument).op();

            // add a typecast for NULL or 0
            if(
              argument.id() == ID_constant &&
              is_null_pointer(to_constant_expr(argument)))
            {
              const typet &comp_type=
                to_union_type(type).components().front().type();

              if(comp_type.id()==ID_pointer)
                argument = typecast_exprt(argument, comp_type);
            }
          }

          ++it;
        }
      }
    }
  }
  else if(expr.id()==ID_constant &&
          expr.type().id()==ID_signedbv)
  {
    #if 0
    const irep_idt &cformat=expr.get(ID_C_cformat);

    if(!cformat.empty())
    {
      declared_enum_constants_mapt::const_iterator entry=
        declared_enum_constants.find(cformat);

      if(entry!=declared_enum_constants.end() &&
         entry->first!=entry->second)
        expr.set(ID_C_cformat, entry->second);
      else if(entry==declared_enum_constants.end() &&
              !std::isdigit(id2string(cformat)[0]))
        expr.remove(ID_C_cformat);
    }
    #endif
  }
  else if(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian)
  {
    const byte_update_exprt &bu = to_byte_update_expr(expr);

    if(bu.op().id() == ID_union && bu.offset().is_zero())
    {
      const union_exprt &union_expr = to_union_expr(bu.op());
      const union_typet &union_type =
        to_union_type(ns.follow(union_expr.type()));

      for(const auto &comp : union_type.components())
      {
        if(bu.value().type() == comp.type())
        {
          exprt member1{ID_member};
          member1.set(ID_component_name, union_expr.get_component_name());
          exprt designated_initializer1{ID_designated_initializer};
          designated_initializer1.add_to_operands(union_expr.op());
          designated_initializer1.add(ID_designator).move_to_sub(member1);

          exprt member2{ID_member};
          member2.set(ID_component_name, comp.get_name());
          exprt designated_initializer2{ID_designated_initializer};
          designated_initializer2.add_to_operands(bu.value());
          designated_initializer2.add(ID_designator).move_to_sub(member2);

          binary_exprt initializer_list{std::move(designated_initializer1),
                                        ID_initializer_list,
                                        std::move(designated_initializer2)};
          expr.swap(initializer_list);

          return;
        }
      }
    }
    else if(
      bu.op().id() == ID_side_effect &&
      to_side_effect_expr(bu.op()).get_statement() == ID_nondet &&
      ns.follow(bu.op().type()).id() == ID_union && bu.offset().is_zero())
    {
      const union_typet &union_type = to_union_type(ns.follow(bu.op().type()));

      for(const auto &comp : union_type.components())
      {
        if(bu.value().type() == comp.type())
        {
          union_exprt union_expr{comp.get_name(), bu.value(), bu.op().type()};
          expr.swap(union_expr);

          return;
        }
      }
    }

    optionalt<exprt> clean_init;
    if(
      ns.follow(bu.type()).id() == ID_union &&
      bu.source_location().get_function().empty())
    {
      clean_init = zero_initializer(bu.op().type(), source_locationt{}, ns)
                     .value_or(nil_exprt{});
      if(clean_init->id() != ID_struct || clean_init->has_operands())
        cleanup_expr(*clean_init);
    }

    if(clean_init.has_value() && bu.op() == *clean_init)
    {
      const union_typet &union_type = to_union_type(ns.follow(bu.type()));

      for(const auto &comp : union_type.components())
      {
        if(bu.value().type() == comp.type())
        {
          union_exprt union_expr{comp.get_name(), bu.value(), bu.type()};
          expr.swap(union_expr);

          return;
        }
      }

      // we still haven't found a suitable component, so just ignore types and
      // build an initializer list without designators
      expr = unary_exprt{ID_initializer_list, bu.value()};
    }
  }
}

void dump_ct::cleanup_type(typet &type)
{
  for(typet &subtype : to_type_with_subtypes(type).subtypes())
    cleanup_type(subtype);

  if(type.id()==ID_code)
  {
    code_typet &code_type=to_code_type(type);

    cleanup_type(code_type.return_type());

    for(code_typet::parameterst::iterator
        it=code_type.parameters().begin();
        it!=code_type.parameters().end();
        ++it)
      cleanup_type(it->type());
  }

  if(type.id()==ID_array)
    cleanup_expr(to_array_type(type).size());

  POSTCONDITION(
    (type.id()!=ID_union && type.id()!=ID_struct) ||
    !type.get(ID_tag).empty());
}

static expr2c_configurationt expr2c_configuration()
{
  // future TODO: with C++20 we can actually use designated initializers as
  // commented out below
  static expr2c_configurationt configuration{
    /* .include_struct_padding_components = */ true,
    /* .print_struct_body_in_type = */ true,
    /* .include_array_size = */ true,
    /* .true_string = */ "1",
    /* .false_string = */ "0",
    /* .use_library_macros = */ true,
    /* .print_enum_int_value = */ false,
    /* .expand_typedef = */ false};

  return configuration;
}

std::string dump_ct::type_to_string(const typet &type)
{
  std::string ret;
  typet t=type;
  cleanup_type(t);

  if(mode == ID_C)
    return type2c(t, ns, expr2c_configuration());
  else if(mode == ID_cpp)
    return type2cpp(t, ns);
  else
    UNREACHABLE;
}

std::string dump_ct::expr_to_string(const exprt &expr)
{
  std::string ret;
  exprt e=expr;
  cleanup_expr(e);

  if(mode == ID_C)
    return expr2c(e, ns, expr2c_configuration());
  else if(mode == ID_cpp)
    return expr2cpp(e, ns);
  else
    UNREACHABLE;
}

void dump_c(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  std::ostream &out)
{
  dump_ct goto2c(
    src, use_system_headers, use_all_headers, include_harness, ns, ID_C);
  out << goto2c;
}

void dump_cpp(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  std::ostream &out)
{
  dump_ct goto2cpp(
    src, use_system_headers, use_all_headers, include_harness, ns, ID_cpp);
  out << goto2cpp;
}

static bool
module_local_declaration(const symbolt &symbol, const std::string module)
{
  std::string base_name =
    get_base_name(id2string(symbol.location.get_file()), true);
  std::string symbol_module = strip_string(id2string(symbol.module));
  return (base_name == module && symbol_module == module);
}

void dump_c_type_header(
  const goto_functionst &src,
  const bool use_system_headers,
  const bool use_all_headers,
  const bool include_harness,
  const namespacet &ns,
  const std::string module,
  std::ostream &out)
{
  symbol_tablet symbol_table = ns.get_symbol_table();
  for(symbol_tablet::iteratort it = symbol_table.begin();
      it != symbol_table.end();
      it++)
  {
    symbolt &new_symbol = it.get_writeable_symbol();
    if(module_local_declaration(new_symbol, module))
    {
      new_symbol.type.set(ID_C_do_not_dump, 0);
    }
    else
    {
      new_symbol.type.set(ID_C_do_not_dump, 1);
    }
  }

  namespacet new_ns(symbol_table);
  dump_ct goto2c(
    src,
    use_system_headers,
    use_all_headers,
    include_harness,
    new_ns,
    ID_C,
    dump_c_configurationt::type_header_configuration);
  out << goto2c;
}
