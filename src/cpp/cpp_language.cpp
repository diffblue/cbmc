/*******************************************************************\

Module: C++ Language Module

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Module

#include "cpp_language.h"

#include <util/config.h>
#include <util/get_base_name.h>
#include <util/symbol_table.h>

#include <ansi-c/ansi_c_entry_point.h>
#include <ansi-c/c_preprocess.h>
#include <linking/linking.h>
#include <linking/remove_internal_symbols.h>

#include "cpp_internal_additions.h"
#include "cpp_parser.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "expr2cpp.h"

#include <cstring>
#include <fstream>

std::set<std::string> cpp_languaget::extensions() const
{
  std::set<std::string> s;

  s.insert("cpp");
  s.insert("CPP");
  s.insert("cc");
  s.insert("cp");
  s.insert("c++");
  s.insert("ii");
  s.insert("cxx");

  #ifndef _WIN32
  s.insert("C");
  #endif

  return s;
}

void cpp_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/// ANSI-C preprocessing
bool cpp_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  if(path.empty())
    return c_preprocess(instream, outstream, message_handler);

  // check extension

  const char *ext=strrchr(path.c_str(), '.');
  if(ext!=nullptr && std::string(ext)==".ipp")
  {
    std::ifstream infile(path);

    char ch;

    while(infile.read(&ch, 1))
      outstream << ch;

    return false;
  }

  return c_preprocess(path, outstream, message_handler);
}

bool cpp_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  // store the path

  parse_path=path;

  // preprocessing

  std::ostringstream o_preprocessed;

  cpp_internal_additions(o_preprocessed);

  if(preprocess(instream, path, o_preprocessed, message_handler))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing
  cpp_parsert cpp_parser{message_handler};
  cpp_parser.set_file(path);
  cpp_parser.in=&i_preprocessed;
  cpp_parser.mode=config.ansi_c.mode;

  bool result=cpp_parser.parse();

  // save result
  cpp_parse_tree.swap(cpp_parser.parse_tree);

  // save some memory
  cpp_parser.clear();

  return result;
}

bool cpp_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  if(module.empty())
    return false;

  symbol_tablet new_symbol_table;

  if(cpp_typecheck(cpp_parse_tree, new_symbol_table, module, message_handler))
    return true;

  remove_internal_symbols(new_symbol_table, message_handler, false);

  return linking(symbol_table, new_symbol_table, message_handler);
}

bool cpp_languaget::generate_support_functions(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  return ansi_c_entry_point(
    symbol_table, message_handler, object_factory_params);
}

void cpp_languaget::show_parse(std::ostream &out, message_handlert &)
{
  for(const auto &i : cpp_parse_tree.items)
    show_parse(out, i);
}

void cpp_languaget::show_parse(
  std::ostream &out,
  const cpp_itemt &item)
{
  if(item.is_linkage_spec())
  {
    const cpp_linkage_spect &linkage_spec=
      item.get_linkage_spec();

    out << "LINKAGE " << linkage_spec.linkage().get(ID_value) << ":\n";

    for(const auto &i : linkage_spec.items())
      show_parse(out, i);

    out << '\n';
  }
  else if(item.is_namespace_spec())
  {
    const cpp_namespace_spect &namespace_spec=
      item.get_namespace_spec();

    out << "NAMESPACE " << namespace_spec.get_namespace()
        << ":\n";

    for(const auto &i : namespace_spec.items())
      show_parse(out, i);

    out << '\n';
  }
  else if(item.is_using())
  {
    const cpp_usingt &cpp_using=item.get_using();

    out << "USING ";
    if(cpp_using.get_namespace())
      out << "NAMESPACE ";
    out << cpp_using.name().pretty() << '\n';
    out << '\n';
  }
  else if(item.is_declaration())
  {
    item.get_declaration().output(out);
  }
  else
    out << "UNKNOWN: " << item.pretty() << '\n';
}

std::unique_ptr<languaget> new_cpp_language()
{
  return std::make_unique<cpp_languaget>();
}

bool cpp_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2cpp(expr, ns);
  return false;
}

bool cpp_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2cpp(type, ns);
  return false;
}

bool cpp_languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &)
{
  name=cpp_type2name(type);
  return false;
}

bool cpp_languaget::to_expr(
  const std::string &code,
  const std::string &,
  exprt &expr,
  const namespacet &ns,
  message_handlert &message_handler)
{
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(code);

  // parsing
  cpp_parsert cpp_parser{message_handler};
  cpp_parser.set_file(irep_idt());
  cpp_parser.in=&i_preprocessed;

  bool result=cpp_parser.parse();

  if(cpp_parser.parse_tree.items.empty())
    result=true;
  else
  {
    // TODO
    // expr.swap(cpp_parser.parse_tree.declarations.front());

    // typecheck it
    result = cpp_typecheck(expr, message_handler, ns);
  }

  // save some memory
  cpp_parser.clear();

  return result;
}

cpp_languaget::~cpp_languaget()
{
}
