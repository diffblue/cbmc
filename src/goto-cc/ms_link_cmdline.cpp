/*******************************************************************\

Module: A special command line object for LINK options

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// A special command line object for LINK options

#include "ms_link_cmdline.h"

#include <cassert>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>

#include <util/unicode.h>

/// parses the command line options into a cmdlinet
/// \par parameters: argument count, argument strings
/// \return none
const char *non_ms_link_options[]=
{
  "--help",
  "--verbosity"
};

bool ms_link_cmdlinet::parse(const std::vector<std::string> &arguments)
{
  for(std::size_t i = 0; i < arguments.size(); i++)
  {
    // is it a non-link option?
    if(std::string(arguments[i], 0, 2) == "--")
    {
      process_non_link_option(arguments[i]);

      if(arguments[i] == "--verbosity")
      {
        if(i < arguments.size() - 1)
        {
          set(arguments[i], arguments[i + 1]);
          i++; // skip ahead
        }
      }
    }
    else if(!arguments[i].empty() && arguments[i][0] == '@')
    {
      // potentially recursive
      process_response_file(std::string(arguments[i], 1, std::string::npos));
    }
    else
      process_link_option(arguments[i]);
  }

  return false;
}

/// parses the command line options into a cmdlinet
/// \par parameters: argument count, argument strings
/// \return none
bool ms_link_cmdlinet::parse(int argc, const char **argv)
{
  // should really use "wide" argv from wmain()

  std::vector<std::string> arguments;

  // skip argv[0]
  for(int i = 1; i < argc; i++)
    arguments.push_back(argv[i]);

  return parse(arguments);
}

static std::istream &my_wgetline(std::istream &in, std::wstring &dest)
{
  // We should support this properly,
  // but will just strip right now.
  dest.clear();

  while(in)
  {
    char ch1, ch2;
    in.get(ch1);
    in.get(ch2);

    if(!in)
    {
      if(!dest.empty())
        in.clear();
      break;
    }

    if(ch1 == '\r')
    {
      // ignore
    }
    else if(ch1 == '\n')
    {
      in.clear();
      break; // line end
    }
    else
      dest += wchar_t(ch1 + (ch2 << 8));
  }

  return in;
}

/// \return none
void ms_link_cmdlinet::process_response_file(const std::string &file)
{
  std::ifstream infile(file);

  if(!infile)
  {
    std::cerr << "failed to open response file `" << file << "'\n";
    return;
  }

  // these may be Unicode -- which is indicated by 0xff 0xfe
  std::string line;
  getline(infile, line);
  if(
    line.size() >= 2 && line[0] == static_cast<char>(0xff) &&
    line[1] == static_cast<char>(0xfe))
  {
    // Unicode, UTF-16 little endian

#if 1
    // Re-open -- should be using wifstream,
    // but this isn't available everywhere.
    std::ifstream infile2(file, std::ios::binary);
    infile2.seekg(2);
    std::wstring wline;

    while(my_wgetline(infile2, wline))
      process_response_file_line(narrow(wline)); // we UTF-8 it

#else

    std::wifstream infile2(file, std::ios::binary);
    std::wstring wline;

    while(std::getline(infile2, wline))
      process_response_file_line(narrow(wline)); // we UTF-8 it

#endif
  }
  else if(
    line.size() >= 3 && line[0] == static_cast<char>(0xef) &&
    line[1] == static_cast<char>(0xbb) && line[2] == static_cast<char>(0xbf))
  {
    // This is the UTF-8 BOM. We can proceed as usual, since
    // we use UTF-8 internally.
    infile.seekg(3);

    while(getline(infile, line))
      process_response_file_line(line);
  }
  else
  {
    // normal ASCII
    infile.seekg(0);
    while(getline(infile, line))
      process_response_file_line(line);
  }
}

/// \return none
void ms_link_cmdlinet::process_response_file_line(const std::string &line)
{
  // In a response file, multiple compiler options and source-code files can
  // appear on one line.  A single compiler-option specification must appear
  // on one line (cannot span multiple lines).  Response files can have
  // comments that begin with the # symbol.

  if(line.empty())
    return;
  if(line[0] == '#')
    return; // comment

  std::vector<std::string> arguments;
  std::string option;
  bool in_quotes = false;
  for(std::size_t i = 0; i < line.size(); i++)
  {
    char ch = line[i];

    if(ch == ' ' && !in_quotes)
    {
      if(!option.empty())
        arguments.push_back(option);
      option.clear();
    }
    else if(ch == '"')
    {
      in_quotes = !in_quotes;
    }
    else
      option += ch;
  }

  if(!option.empty())
    arguments.push_back(option);

  parse(arguments);
}

/// \return none
void ms_link_cmdlinet::process_non_link_option(const std::string &s)
{
  set(s);

  for(const auto & opt : non_ms_link_options)
    if(s == opt)
      return;

  // unrecognized option
  std::cout << "Warning: uninterpreted non-LINK option `" << s << "'\n";
}

const char *ms_link_options[] = {
  "ALIGN",
  "ALLOWBIND",
  "ALLOWISOLATION",
  "APPCONTAINER",
  "ASSEMBLYDEBUG",
  "ASSEMBLYLINKRESOURCE",
  "ASSEMBLYMODULE",
  "ASSEMBLYRESOURCE",
  "BASE",
  "CLRIMAGETYPE",
  "CLRLOADEROPTIMIZATION",
  "CLRSUPPORTLASTERROR",
  "CLRTHREADATTRIBUTE",
  "CLRUNMANAGEDCODECHECK",
  "DEBUG",
  "DEF",
  "DEFAULTLIB",
  "DELAY",
  "DELAYLOAD",
  "DELAYSIGN",
  "DLL",
  "DRIVER",
  "DYNAMICBASE",
  "ENTRY",
  "ERRORREPORT",
  "EXPORT",
  "EXPORTPADMIN",
  "FASTGENPROFILE",
  "FIXED",
  "FORCE",
  "FUNCTIONPADMIN",
  "GUARD",
  "GENPROFILE",
  "HEAP",
  "HIGHENTROPYVA",
  "IDLOUT",
  "IGNORE",
  "IGNOREIDL",
  "IMPLIB",
  "INCLUDE",
  "INCREMENTAL",
  "INTEGRITYCHECK",
  "KERNEL",
  "KEYCONTAINER",
  "KEYFILE",
  "LARGEADDRESSAWARE",
  "LIBPATH",
  "LTCG",
  "MACHINE",
  "MANIFEST",
  "MANIFESTDEPENDENCY",
  "MANIFESTFILE",
  "MANIFESTINPUT",
  "MANIFESTUAC",
  "MAP",
  "MAPINFO",
  "MERGE",
  "MIDL",
  "NOASSEMBLY",
  "NODEFAULTLIB",
  "NOENTRY",
  "NOIMPLIB",
  "NOLOGO",
  "NXCOMPAT",
  "OPT",
  "ORDER",
  "OUT",
  "PDB",
  "PDBSTRIPPED",
  "PROFILE",
  "RELEASE",
  "SAFESEH",
  "SECTION",
  "STACK",
  "STUB",
  "SUBSYSTEM",
  "SWAPRUN",
  "TLBID",
  "TLBOUT",
  "TIME",
  "TSAWARE",
  "USEPROFILE",
  "VERBOSE",
  "VERSION",
  "WINMD",
  "WINMDDELAYSIGN",
  "WINMDFILE",
  "WINMDKEYCONTAINER",
  "WINMDKEYFILE",
  "WHOLEARCHIVE",
  "WX"
};

static std::string to_upper_string(const std::string &s)
{
  std::string result = s;
  transform(result.begin(), result.end(), result.begin(), toupper);
  return result;
}

void ms_link_cmdlinet::process_link_option(const std::string &s)
{
  if(s == "")
    return;

  if(s[0] != '/' && s[0] != '-')
  {
    args.push_back(s);
    return;
  }

  for(const std::string &ms_link_option : ms_link_options)
  {
    // These are case insensitive.
    if(
      to_upper_string(std::string(s, 1, std::string::npos)) == ms_link_option ||
      to_upper_string(std::string(s, 1, ms_link_option.size() + 1)) == ms_link_option + ':')
    {
      optionalt<std::size_t> optnr = getoptnr(ms_link_option);

      if(!optnr.has_value())
      {
        cmdlinet::optiont option;
        option.islong = true;
        option.optstring = ms_link_option;
        option.optchar = 0;
        options.push_back(option);
        optnr = options.size() - 1;
      }

      options[*optnr].isset = true;

      if(s.size() > ms_link_option.size() + 1)
        options[*optnr].values.push_back(
          std::string(s, ms_link_option.size() + 2, std::string::npos));

      return;
    }
  }

  // unrecognized option
  std::cout << "Warning: uninterpreted LINK option `" << s << "'\n";
}
