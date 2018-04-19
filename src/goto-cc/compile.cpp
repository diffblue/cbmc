/*******************************************************************\

Module: Compile and link source and object files.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Compile and link source and object files.

#include "compile.h"

#include <cstring>
#include <fstream>
#include <iostream>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/file_util.h>
#include <util/get_base_name.h>
#include <util/suffix.h>
#include <util/tempdir.h>
#include <util/unicode.h>
#include <util/version.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/ansi_c_entry_point.h>

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>

#include <langapi/mode.h>

#include <linking/static_lifetime_init.h>

#define DOTGRAPHSETTINGS  "color=black;" \
                          "orientation=portrait;" \
                          "fontsize=20;"\
                          "compound=true;"\
                          "size=\"30,40\";"\
                          "ratio=compress;"

// the following are for chdir

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#ifdef _WIN32
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <direct.h>
#include <windows.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#include <util/pragma_pop.def>
#endif

/// reads and source and object files, compiles and links them into goto program
/// objects.
/// \return true on error, false otherwise
bool compilet::doit()
{
  compiled_functions.clear();

  add_compiler_specific_defines(config);

  // Parse command line for source and object file names
  for(std::size_t i=0; i<_cmdline.args.size(); i++)
    if(add_input_file(_cmdline.args[i]))
      return true;

  for(std::list<std::string>::const_iterator it = libraries.begin();
      it!=libraries.end();
      it++)
  {
    if(!find_library(*it))
      // GCC is going to complain if this doesn't exist
      debug() << "Library not found: " << *it << " (ignoring)" << eom;
  }

  statistics() << "No. of source files: " << source_files.size() << eom;
  statistics() << "No. of object files: " << object_files.size() << eom;

  // Work through the given source files

  if(source_files.empty() && object_files.empty())
  {
    error() << "no input files" << eom;
    return true;
  }

  if(mode==LINK_LIBRARY && !source_files.empty())
  {
    error() << "cannot link source files" << eom;
    return true;
  }

  if(mode==PREPROCESS_ONLY && !object_files.empty())
  {
    error() << "cannot preprocess object files" << eom;
    return true;
  }

  const unsigned warnings_before=
    get_message_handler().get_message_count(messaget::M_WARNING);

  if(!source_files.empty())
    if(compile())
      return true;

  if(mode==LINK_LIBRARY ||
     mode==COMPILE_LINK ||
     mode==COMPILE_LINK_EXECUTABLE)
  {
    if(link())
      return true;
  }

  return
    warning_is_fatal &&
    get_message_handler().get_message_count(messaget::M_WARNING)!=
    warnings_before;
}

enum class file_typet
{
  FAILED_TO_OPEN_FILE,
  UNKNOWN,
  SOURCE_FILE,
  NORMAL_ARCHIVE,
  THIN_ARCHIVE,
  GOTO_BINARY,
  ELF_OBJECT
};

static file_typet detect_file_type(const std::string &file_name)
{
  // first of all, try to open the file
  std::ifstream in(file_name);
  if(!in)
    return file_typet::FAILED_TO_OPEN_FILE;

  const std::string::size_type r = file_name.rfind('.');

  const std::string ext =
    r == std::string::npos ? "" : file_name.substr(r + 1, file_name.length());

  if(
    ext == "c" || ext == "cc" || ext == "cp" || ext == "cpp" || ext == "CPP" ||
    ext == "c++" || ext == "C" || ext == "i" || ext == "ii" || ext == "class" ||
    ext == "jar" || ext == "jsil")
  {
    return file_typet::SOURCE_FILE;
  }

  char hdr[8];
  in.get(hdr, 8);
  if((ext == "a" || ext == "o") && strncmp(hdr, "!<thin>", 8) == 0)
    return file_typet::THIN_ARCHIVE;

  if(ext == "a")
    return file_typet::NORMAL_ARCHIVE;

  if(is_goto_binary(file_name))
    return file_typet::GOTO_BINARY;

  if(hdr[0] == 0x7f && memcmp(hdr + 1, "ELF", 3) == 0)
    return file_typet::ELF_OBJECT;

  return file_typet::UNKNOWN;
}

/// puts input file names into a list and does preprocessing for libraries.
/// \return false on success, true on error.
bool compilet::add_input_file(const std::string &file_name)
{
  switch(detect_file_type(file_name))
  {
  case file_typet::FAILED_TO_OPEN_FILE:
    warning() << "failed to open file `" << file_name
              << "': " << std::strerror(errno) << eom;
    return warning_is_fatal; // generously ignore unless -Werror

  case file_typet::UNKNOWN:
    // unknown extension, not a goto binary, will silently ignore
    debug() << "unknown file type in `" << file_name << "'" << eom;
    return false;

  case file_typet::ELF_OBJECT:
    // ELF file without goto-cc section, silently ignore
    debug() << "ELF object without goto-cc section: `" << file_name << "'"
            << eom;
    return false;

  case file_typet::SOURCE_FILE:
    source_files.push_back(file_name);
    return false;

  case file_typet::NORMAL_ARCHIVE:
    return add_files_from_archive(file_name, false);

  case file_typet::THIN_ARCHIVE:
    return add_files_from_archive(file_name, true);

  case file_typet::GOTO_BINARY:
    object_files.push_back(file_name);
    return false;
  }

  UNREACHABLE;
}

/// extracts goto binaries from AR archive and add them as input files.
/// \return false on success, true on error.
bool compilet::add_files_from_archive(
  const std::string &file_name,
  bool thin_archive)
{
  std::stringstream cmd;
  FILE *stream;

  std::string tstr = working_directory;

  if(!thin_archive)
  {
    tstr = get_temporary_directory("goto-cc.XXXXXX");

    if(tstr=="")
    {
      error() << "Cannot create temporary directory" << eom;
      return true;
    }

    tmp_dirs.push_back(tstr);
    if(chdir(tmp_dirs.back().c_str())!=0)
    {
      error() << "Cannot switch to temporary directory" << eom;
      return true;
    }

    // unpack now
    cmd << "ar x " << concat_dir_file(working_directory, file_name);

    stream=popen(cmd.str().c_str(), "r");
    pclose(stream);

    cmd.clear();
    cmd.str("");
  }

  // add the files from "ar t"
  cmd << "ar t " << concat_dir_file(working_directory, file_name);

  stream = popen(cmd.str().c_str(), "r");

  if(stream != nullptr)
  {
    std::string line;
    int ch; // fgetc returns an int, not char
    while((ch = fgetc(stream)) != EOF)
    {
      if(ch != '\n')
      {
        line += static_cast<char>(ch);
      }
      else
      {
        std::string t = concat_dir_file(tstr, line);

        if(is_goto_binary(t))
          object_files.push_back(t);
        else
          debug() << "Object file is not a goto binary: " << line << eom;

        line = "";
      }
    }

    pclose(stream);
  }

  if(!thin_archive && chdir(working_directory.c_str()) != 0)
    error() << "Could not change back to working directory" << eom;

  return false;
}

/// tries to find a library object file that matches the given library name.
/// \par parameters: library name
/// \return true if found, false otherwise
bool compilet::find_library(const std::string &name)
{
  std::string tmp;

  for(std::list<std::string>::const_iterator
      it=library_paths.begin();
      it!=library_paths.end();
      it++)
  {
    #ifdef _WIN32
    tmp = *it + "\\lib";
    #else
    tmp = *it + "/lib";
    #endif

    std::ifstream in(tmp+name+".a");

    if(in.is_open())
      return !add_input_file(tmp+name+".a");
    else
    {
      std::string libname=tmp+name+".so";

      switch(detect_file_type(libname))
      {
      case file_typet::GOTO_BINARY:
        return !add_input_file(libname);

      case file_typet::ELF_OBJECT:
        warning() << "Warning: Cannot read ELF library " << libname << eom;
        return warning_is_fatal;

      default:
        break;
      }
    }
  }

  return false;
}

/// parses object files and links them
/// \return true on error, false otherwise
bool compilet::link()
{
  // "compile" hitherto uncompiled functions
  statistics() << "Compiling functions" << eom;
  convert_symbols(compiled_functions);

  // parse object files
  for(const auto &file_name : object_files)
  {
    if(read_object_and_link(file_name, symbol_table,
                            compiled_functions, get_message_handler()))
      return true;
  }

  // produce entry point?

  if(mode==COMPILE_LINK_EXECUTABLE)
  {
    // new symbols may have been added to a previously linked file
    // make sure a new entry point is created that contains all
    // static initializers
    compiled_functions.function_map.erase(INITIALIZE_FUNCTION);

    symbol_table.remove(goto_functionst::entry_point());
    compiled_functions.function_map.erase(goto_functionst::entry_point());

    if(ansi_c_entry_point(symbol_table, get_message_handler()))
      return true;

    // entry_point may (should) add some more functions.
    convert_symbols(compiled_functions);
  }

  if(write_object_file(
      output_file_executable, symbol_table, compiled_functions))
    return true;

  return add_written_cprover_symbols(symbol_table);
}

/// parses source files and writes object files, or keeps the symbols in the
/// symbol_table depending on the doLink flag.
/// \return true on error, false otherwise
bool compilet::compile()
{
  while(!source_files.empty())
  {
    std::string file_name=source_files.front();
    source_files.pop_front();

    // Visual Studio always prints the name of the file it's doing
    // onto stdout. The name of the directory is stripped.
    if(echo_file_name)
      std::cout << get_base_name(file_name, false) << '\n' << std::flush;

    bool r=parse_source(file_name); // don't break the program!

    if(r)
    {
      const std::string &debug_outfile=
        cmdline.get_value("print-rejected-preprocessed-source");
      if(!debug_outfile.empty())
      {
        std::ifstream in(file_name, std::ios::binary);
        std::ofstream out(debug_outfile, std::ios::binary);
        out << in.rdbuf();
        warning() << "Failed sources in " << debug_outfile << eom;
      }

      return true; // parser/typecheck error
    }

    if(mode==COMPILE_ONLY || mode==ASSEMBLE_ONLY)
    {
      // output an object file for every source file

      // "compile" functions
      convert_symbols(compiled_functions);

      std::string cfn;

      if(output_file_object=="")
      {
        const std::string file_name_with_obj_ext =
          get_base_name(file_name, true) + "." + object_file_extension;

        if(!output_directory_object.empty())
          cfn = concat_dir_file(output_directory_object, file_name_with_obj_ext);
        else
          cfn = file_name_with_obj_ext;
      }
      else
        cfn = output_file_object;

      if(write_object_file(cfn, symbol_table, compiled_functions))
        return true;

      if(add_written_cprover_symbols(symbol_table))
        return true;

      symbol_table.clear(); // clean symbol table for next source file.
      compiled_functions.clear();
    }
  }

  return false;
}

/// parses a source file (low-level parsing)
/// \return true on error, false otherwise
bool compilet::parse(const std::string &file_name)
{
  if(file_name=="-")
    return parse_stdin();

  #ifdef _MSC_VER
  std::ifstream infile(widen(file_name));
  #else
  std::ifstream infile(file_name);
  #endif

  if(!infile)
  {
    error() << "failed to open input file `" << file_name << "'" << eom;
    return true;
  }

  std::unique_ptr<languaget> languagep;

  // Using '-x', the type of a file can be overridden;
  // otherwise, it's guessed from the extension.

  if(override_language!="")
  {
    if(override_language=="c++" || override_language=="c++-header")
      languagep = get_language_from_mode(ID_cpp);
    else
      languagep = get_language_from_mode(ID_C);
  }
  else
    languagep=get_language_from_filename(file_name);

  if(languagep==nullptr)
  {
    error() << "failed to figure out type of file `" << file_name << "'" << eom;
    return true;
  }

  languagep->set_message_handler(get_message_handler());

  language_filet &lf=language_files.add_file(file_name);
  lf.language=std::move(languagep);

  if(mode==PREPROCESS_ONLY)
  {
    statistics() << "Preprocessing: " << file_name << eom;

    std::ostream *os = &std::cout;
    std::ofstream ofs;

    if(cmdline.isset('o'))
    {
      ofs.open(cmdline.get_value('o'));
      os = &ofs;

      if(!ofs.is_open())
      {
        error() << "failed to open output file `"
                << cmdline.get_value('o') << "'" << eom;
        return true;
      }
    }

    lf.language->preprocess(infile, file_name, *os);
  }
  else
  {
    statistics() << "Parsing: " << file_name << eom;

    if(lf.language->parse(infile, file_name))
    {
      if(get_ui()==ui_message_handlert::uit::PLAIN)
        error() << "PARSING ERROR" << eom;
      return true;
    }
  }

  lf.get_modules();
  return false;
}

/// parses a source file (low-level parsing)
/// \return true on error, false otherwise
bool compilet::parse_stdin()
{
  ansi_c_languaget language;

  language.set_message_handler(get_message_handler());

  statistics() << "Parsing: (stdin)" << eom;

  if(mode==PREPROCESS_ONLY)
  {
    std::ostream *os = &std::cout;
    std::ofstream ofs;

    if(cmdline.isset('o'))
    {
      ofs.open(cmdline.get_value('o'));
      os = &ofs;

      if(!ofs.is_open())
      {
        error() << "failed to open output file `"
                << cmdline.get_value('o') << "'" << eom;
        return true;
      }
    }

    language.preprocess(std::cin, "", *os);
  }
  else
  {
    if(language.parse(std::cin, ""))
    {
      if(get_ui()==ui_message_handlert::uit::PLAIN)
        error() << "PARSING ERROR" << eom;
      return true;
    }
  }

  return false;
}

/// writes the goto functions in the function table to a binary format object
/// file.
/// \par parameters: file_name, functions table
/// \return true on error, false otherwise
bool compilet::write_object_file(
  const std::string &file_name,
  const symbol_tablet &lsymbol_table,
  goto_functionst &functions)
{
  return write_bin_object_file(file_name, lsymbol_table, functions);
}

/// writes the goto functions in the function table to a binary format object
/// file.
/// \par parameters: file_name, functions table
/// \return true on error, false otherwise
bool compilet::write_bin_object_file(
  const std::string &file_name,
  const symbol_tablet &lsymbol_table,
  goto_functionst &functions)
{
  statistics() << "Writing binary format object `"
               << file_name << "'" << eom;

  // symbols
  statistics() << "Symbols in table: "
               << lsymbol_table.symbols.size() << eom;

  std::ofstream outfile(file_name, std::ios::binary);

  if(!outfile.is_open())
  {
    error() << "Error opening file `" << file_name << "'" << eom;
    return true;
  }

  if(write_goto_binary(outfile, lsymbol_table, functions))
    return true;

  unsigned cnt=function_body_count(functions);

  statistics() << "Functions: " << functions.function_map.size()
               << "; " << cnt << " have a body." << eom;

  outfile.close();
  wrote_object=true;

  return false;
}

/// parses a source file
/// \return true on error, false otherwise
bool compilet::parse_source(const std::string &file_name)
{
  if(parse(file_name))
    return true;

  if(typecheck()) // we just want to typecheck this one file here
    return true;

  if((has_suffix(file_name, ".class") ||
      has_suffix(file_name, ".jar")) &&
     final())
    return true;

  // so we remove it from the list afterwards
  language_files.remove_file(file_name);
  return false;
}

/// constructor
/// \return nothing
compilet::compilet(cmdlinet &_cmdline, ui_message_handlert &mh, bool Werror):
  language_uit(_cmdline, mh),
  ns(symbol_table),
  cmdline(_cmdline),
  warning_is_fatal(Werror)
{
  mode=COMPILE_LINK_EXECUTABLE;
  echo_file_name=false;
  wrote_object=false;
  working_directory=get_current_working_directory();
}

/// cleans up temporary files
/// \return nothing
compilet::~compilet()
{
  // clean up temp dirs

  for(std::list<std::string>::const_iterator it = tmp_dirs.begin();
      it!=tmp_dirs.end();
      it++)
    delete_directory(*it);
}

unsigned compilet::function_body_count(const goto_functionst &functions) const
{
  int fbs=0;

  for(goto_functionst::function_mapt::const_iterator it=
      functions.function_map.begin();
      it != functions.function_map.end();
      it++)
    if(it->second.body_available())
      fbs++;

  return fbs;
}

void compilet::add_compiler_specific_defines(configt &config) const
{
  config.ansi_c.defines.push_back(
    std::string("__GOTO_CC_VERSION__=") + CBMC_VERSION);
}

void compilet::convert_symbols(goto_functionst &dest)
{
  goto_convert_functionst converter(symbol_table, get_message_handler());

  // the compilation may add symbols!

  symbol_tablet::symbolst::size_type before=0;

  while(before!=symbol_table.symbols.size())
  {
    before=symbol_table.symbols.size();

    typedef std::set<irep_idt> symbols_sett;
    symbols_sett symbols;

    for(const auto &named_symbol : symbol_table.symbols)
      symbols.insert(named_symbol.first);

    // the symbol table iterators aren't stable
    for(symbols_sett::const_iterator
        it=symbols.begin();
        it!=symbols.end();
        ++it)
    {
      symbol_tablet::symbolst::const_iterator s_it=
        symbol_table.symbols.find(*it);
      assert(s_it!=symbol_table.symbols.end());

      if(
        s_it->second.is_function() && !s_it->second.is_compiled() &&
        s_it->second.value.is_not_nil())
      {
        debug() << "Compiling " << s_it->first << eom;
        converter.convert_function(s_it->first, dest.function_map[s_it->first]);
        symbol_table.get_writeable_ref(*it).set_compiled();
      }
    }
  }
}

bool compilet::add_written_cprover_symbols(const symbol_tablet &symbol_table)
{
  for(const auto &pair : symbol_table.symbols)
  {
    const irep_idt &name=pair.second.name;
    const typet &new_type=pair.second.type;
    if(!(has_prefix(id2string(name), CPROVER_PREFIX) && new_type.id()==ID_code))
      continue;

    bool inserted;
    std::map<irep_idt, symbolt>::iterator old;
    std::tie(old, inserted)=written_macros.insert({name, pair.second});

    if(!inserted && old->second.type!=new_type)
    {
      error() << "Incompatible CPROVER macro symbol types:" << eom
              << old->second.type.pretty() << "(at " << old->second.location
              << ")" << eom << "and" << eom << new_type.pretty()
              << "(at " << pair.second.location << ")" << eom;
      return true;
    }
  }
  return false;
}
