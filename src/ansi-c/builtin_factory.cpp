/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "builtin_factory.h"
#include "ansi_c_internal_additions.h"

#include "ansi_c_parser.h"
#include "ansi_c_typecheck.h"

#include <util/config.h>
#include <util/prefix.h>
#include <util/string_utils.h>

#include <sstream>

static bool find_pattern(
  const std::string &pattern,
  const char *header_file,
  std::ostream &out)
{
  std::istringstream hdr(header_file);
  std::string line;
  while(std::getline(hdr, line))
  {
    line = strip_string(line);
    if(has_prefix(line, "//") || line.find(pattern) == std::string::npos)
      continue;

    out << line;
    return true;
  }

  return false;
}

static bool convert(
  const irep_idt &identifier,
  const std::ostringstream &s,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  std::istringstream in(s.str());

  ansi_c_parser.clear();
  ansi_c_parser.set_file(ID_built_in);
  ansi_c_parser.in=&in;
  ansi_c_parser.set_message_handler(message_handler);
  ansi_c_parser.for_has_scope=config.ansi_c.for_has_scope;
  ansi_c_parser.cpp98=false; // it's not C++
  ansi_c_parser.cpp11=false; // it's not C++
  ansi_c_parser.mode=config.ansi_c.mode;

  ansi_c_scanner_init();

  if(ansi_c_parser.parse())
    return true;

  symbol_tablet new_symbol_table;

  // this is recursive -- builtin_factory is called
  // from the typechecker
  if(ansi_c_typecheck(
    ansi_c_parser.parse_tree,
    new_symbol_table,
    "", // module
    message_handler))
  {
    return true;
  }

  // we should now have a new symbol
  symbol_tablet::symbolst::const_iterator s_it=
    new_symbol_table.symbols.find(identifier);

  if(s_it==new_symbol_table.symbols.end())
  {
    messaget message(message_handler);
    message.error() << "failed to produce built-in symbol '" << identifier
                    << '\'' << messaget::eom;
    return true;
  }

  // copy the new symbol
  symbol_table.add(s_it->second);

  return false;
}

//! Check whether given identifier is a compiler built-in.
//! If so, add declaration to symbol table.
//! \return 'true' on error
bool builtin_factory(
  const irep_idt &identifier,
  symbol_tablet &symbol_table,
  message_handlert &mh)
{
  // we search for "space" "identifier" "("
  const std::string pattern=' '+id2string(identifier)+'(';

  std::ostringstream s;

  std::string code;
  ansi_c_internal_additions(code);
  s << code;

  // our own extensions
  if(find_pattern(pattern, cprover_builtin_headers, s))
    return convert(identifier, s, symbol_table, mh);

  // this is Visual C/C++ only
  if(config.ansi_c.os==configt::ansi_ct::ost::OS_WIN)
  {
    if(find_pattern(pattern, windows_builtin_headers, s))
      return convert(identifier, s, symbol_table, mh);
  }

  // ARM stuff
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::ARM)
  {
    if(find_pattern(pattern, arm_builtin_headers, s))
      return convert(identifier, s, symbol_table, mh);
  }

  // CW stuff
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::CODEWARRIOR)
  {
    if(find_pattern(pattern, cw_builtin_headers, s))
      return convert(identifier, s, symbol_table, mh);
  }

  // GCC junk stuff, also for CLANG and ARM
  if(
    config.ansi_c.mode == configt::ansi_ct::flavourt::GCC ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::ARM)
  {
    if(find_pattern(pattern, gcc_builtin_headers_generic, s))
      return convert(identifier, s, symbol_table, mh);

    if(find_pattern(pattern, gcc_builtin_headers_math, s))
      return convert(identifier, s, symbol_table, mh);

    if(find_pattern(pattern, gcc_builtin_headers_mem_string, s))
      return convert(identifier, s, symbol_table, mh);

    if(find_pattern(pattern, gcc_builtin_headers_omp, s))
      return convert(identifier, s, symbol_table, mh);

    if(find_pattern(pattern, gcc_builtin_headers_tm, s))
      return convert(identifier, s, symbol_table, mh);

    if(find_pattern(pattern, gcc_builtin_headers_ubsan, s))
      return convert(identifier, s, symbol_table, mh);

    if(find_pattern(pattern, clang_builtin_headers, s))
      return convert(identifier, s, symbol_table, mh);

    if(config.ansi_c.arch=="i386" ||
       config.ansi_c.arch=="x86_64" ||
       config.ansi_c.arch=="x32")
    {
      if(find_pattern(pattern, gcc_builtin_headers_ia32, s))
        return convert(identifier, s, symbol_table, mh);

      if(find_pattern(pattern, gcc_builtin_headers_ia32_2, s))
        return convert(identifier, s, symbol_table, mh);

      if(find_pattern(pattern, gcc_builtin_headers_ia32_3, s))
        return convert(identifier, s, symbol_table, mh);

      if(find_pattern(pattern, gcc_builtin_headers_ia32_4, s))
        return convert(identifier, s, symbol_table, mh);

      if(find_pattern(pattern, gcc_builtin_headers_ia32_5, s))
        return convert(identifier, s, symbol_table, mh);
    }
    else if(config.ansi_c.arch=="arm64" ||
            config.ansi_c.arch=="armel" ||
            config.ansi_c.arch=="armhf" ||
            config.ansi_c.arch=="arm")
    {
      if(find_pattern(pattern, gcc_builtin_headers_arm, s))
        return convert(identifier, s, symbol_table, mh);
    }
    else if(config.ansi_c.arch=="mips64el" ||
            config.ansi_c.arch=="mipsn32el" ||
            config.ansi_c.arch=="mipsel" ||
            config.ansi_c.arch=="mips64" ||
            config.ansi_c.arch=="mipsn32" ||
            config.ansi_c.arch=="mips")
    {
      if(find_pattern(pattern, gcc_builtin_headers_mips, s))
        return convert(identifier, s, symbol_table, mh);
    }
    else if(config.ansi_c.arch=="powerpc" ||
            config.ansi_c.arch=="ppc64" ||
            config.ansi_c.arch=="ppc64le")
    {
      if(find_pattern(pattern, gcc_builtin_headers_power, s))
        return convert(identifier, s, symbol_table, mh);
    }
  }

  return true;
}
