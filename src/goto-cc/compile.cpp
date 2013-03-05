/*******************************************************************\

Module: Compile and link source and object files.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#include <fstream>
#include <sstream>
#include <cstdlib>
#include <algorithm>

#include <config.h>
#include <tempdir.h>
#include <replace_symbol.h>
#include <base_type.h>
#include <i2string.h>
#include <cmdline.h>
#include <file_util.h>
#include <unicode.h>

#include <ansi-c/ansi_c_language.h>
#include <linking/linking_class.h>
#include <linking/entry_point.h>

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/goto_function_serialization.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>

#include <langapi/mode.h>

#include <irep_serialization.h>
#include <symbol_serialization.h>

#include "get_base_name.h"
#include "compile.h"
#include "version.h"

#define DOTGRAPHSETTINGS  "color=black;" \
                          "orientation=portrait;" \
                          "fontsize=20;"\
                          "compound=true;"\
                          "size=\"30,40\";"\
                          "ratio=compress;"

// the following are for chdir

#ifdef __linux__
#include <unistd.h>
#endif

#ifdef __FreeBSD_kernel__
#include <unistd.h>
#endif

#ifdef __MACH__
#include <unistd.h>
#endif

#ifdef __CYGWIN__
#include <unistd.h>
#endif

#ifdef _WIN32
#include <direct.h>
#include <windows.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#endif

/*******************************************************************\

Function: compilet::doit

  Inputs: none

 Outputs: true on error, false otherwise

 Purpose: reads and source and object files, compiles and links them
          into goto program objects.

\*******************************************************************/

bool compilet::doit()
{
  compiled_functions.clear();

  add_compiler_specific_defines(config);

  // Parse commandline for source and object file names
  for(unsigned i=0; i<_cmdline.args.size(); i++)
    if(add_input_file(_cmdline.args[i]))
      return true;

  for(std::list<std::string>::const_iterator it = libraries.begin();
      it!=libraries.end();
      it++)
  {
    if(!find_library(*it))
      warning(std::string("Library not found: ") + *it + " (ignoring)");
  }

  // Work through the given source files
  print(8, "No. of source files: " +
    i2string((unsigned long) source_files.size()));

  print(8, "No. of object files: " +
    i2string((unsigned long) object_files.size()));

  if(source_files.size()==0 && object_files.size()==0)
  {
    error("no input files");
    return true;
  }

  if(mode==LINK_LIBRARY && source_files.size()>0)
  {
    error("cannot link source files");
    return true;
  }

  if(mode==PREPROCESS_ONLY && object_files.size()>0)
  {
    error("cannot preprocess object files");
    return true;
  }

  if(source_files.size()>0)
    if(compile()) return true;

  if(mode==LINK_LIBRARY ||
     mode==COMPILE_LINK ||
     mode==COMPILE_LINK_EXECUTABLE)
  {
    if(link()) return true;
  }
  
  return false;
}

/*******************************************************************\

Function: compilet::add_input_file

  Inputs: none

 Outputs: false on success, true on error.

 Purpose: puts input file names into a list and does preprocessing for
          libraries.

\*******************************************************************/

bool compilet::add_input_file(const std::string &file_name)
{
  size_t r=file_name.rfind('.', file_name.length()-1);

  if(r!=std::string::npos)
  {
    std::string ext = file_name.substr(r+1, file_name.length());

    if(ext=="c" ||
       ext=="cc" ||
       ext=="cp" ||
       ext=="cpp" ||
       ext=="CPP" ||
       ext=="c++" ||
       ext=="C" ||
       ext=="i" ||
       ext=="ii")
    {
      source_files.push_back(file_name);
    }
    else if(ext=="a")
    {
      #ifdef _WIN32
      char td[MAX_PATH+1];
      #else
      char td[] = "goto-cc.XXXXXX";
      #endif

      std::string tstr=get_temporary_directory(td);

      if(tstr=="")
      {
        error("Cannot create temporary directory");
        return true;
      }

      tmp_dirs.push_back(tstr);
      std::stringstream cmd("");
      if(chdir(tmp_dirs.back().c_str())!=0)
      {
        error("Cannot switch to temporary directory");
        return true;
      }

      // unpack now
      #ifdef _WIN32
      if(file_name[0]!='/' && file_name[1]!=':')
      #else
      if(file_name[0]!='/')
      #endif
      {
        cmd << "ar x " <<
        #ifdef _WIN32
          working_directory << "\\" << file_name;
        #else
          working_directory << "/" << file_name;
        #endif
      }
      else
      {
        cmd << "ar x " << file_name;
      }
      
      FILE *stream;

      stream=popen(cmd.str().c_str(), "r");
      pclose(stream);
      
      cmd.clear();
      cmd.str("");
      
      // add the files from "ar t"
      #ifdef _WIN32
      if(file_name[0]!='/' && file_name[1]!=':')
      #else
      if(file_name[0]!='/')
      #endif
      {
        cmd << "ar t " <<
        #ifdef _WIN32
          working_directory << "\\" << file_name;
        #else
          working_directory << "/" << file_name;
        #endif
      }
      else
      {
        cmd << "ar t " << file_name;
      }

      stream=popen(cmd.str().c_str(), "r");
      if(stream!=NULL)
      {
        std::string line;
        char ch;
        while((ch=fgetc(stream))!=EOF)
        {
          if(ch!='\n' && ch!=EOF)
          {
            line += ch;
          }
          else
          {
            std::string t;
            #ifdef _WIN32
            t = tmp_dirs.back() + '\\' + line;
            #else
            t = tmp_dirs.back() + '/' + line;
            #endif

            if(is_goto_binary(t))
              object_files.push_back(t);
            line = "";
          }
        }
      }
      pclose(stream);
      cmd.str("");

      if(chdir(working_directory.c_str())!=0)
        error("Could not change back to working directory.");
    }
    else if(is_goto_binary(file_name))
      object_files.push_back(file_name);
    else
    {
      // unknown extension, not a goto binary, will ignore
    }
  }
  else
  {
    // don't care about no extensions
  }

  return false;
}

/*******************************************************************\

Function: compilet::find_library

  Inputs: library name

 Outputs: true if found, false otherwise

 Purpose: tries to find a library object file that matches the given
          library name.

\*******************************************************************/

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

    std::ifstream in((tmp+name+".a").c_str());

    if(in.is_open())
      add_input_file(tmp+name+".a");
    else
    {
      std::string libname=tmp+name+".so";

      if(is_goto_binary(libname))
        add_input_file(libname);
      else if(is_elf_file(libname))
        std::cout << "Warning: Cannot read ELF library " << libname
                  << std::endl;
      else
        return false;
    }
  }
  
  return true;
}

/*******************************************************************\

Function: compilet::is_elf_file

  Inputs: file name

 Outputs: true if the given file name exists and is an ELF file,
          false otherwise

 Purpose: checking if we can load an object file

\*******************************************************************/

bool compilet::is_elf_file(const std::string &file_name)
{
  std::fstream in;

  in.open(file_name.c_str(), std::ios::in);
  if(in.is_open())
  {
    char buf[4];
    for (unsigned i=0; i<4; i++)
      buf[i] = in.get();
    if(buf[0]==0x7f && buf[1]=='E' &&
        buf[2]=='L' && buf[3]=='F')
      return true;
  }

  return false;
}

/*******************************************************************\

Function: compilet::link

  Inputs: none

 Outputs: true on error, false otherwise

 Purpose: parses object files and links them

\*******************************************************************/

bool compilet::link()
{
  // "compile" hitherto uncompiled functions
  print(8, "Compiling functions");
  convert_symbols(compiled_functions);

  // parse object files
  while(object_files.size()>0)
  {
    std::string file_name=object_files.front();
    object_files.pop_front();

    if(read_object(file_name, compiled_functions))
      return true;
  }

  // produce entry point?
  
  if(mode==COMPILE_LINK_EXECUTABLE)
  {
    if(entry_point(symbol_table, "c::main", ui_message_handler))
      return true;

    // entry_point may (should) add some more functions.
    convert_symbols(compiled_functions);
  }

  if(write_object_file(output_file_executable, symbol_table, compiled_functions))
    return true;

  return false;
}

/*******************************************************************\

Function: compilet::compile

  Inputs: none

 Outputs: true on error, false otherwise

 Purpose: parses source files and writes object files, or keeps the
          symbols in the symbol_table depending on the doLink flag.

\*******************************************************************/

bool compilet::compile()
{
  while(!source_files.empty())
  {
    std::string file_name=source_files.front();
    source_files.pop_front();
    
    // Visual Studio always prints the name of the file it's doing
    if(echo_file_name)
      status(file_name);

    bool r=parse_source(file_name); // don't break the program!

    if(r) return true; // parser/typecheck error

    if(mode==COMPILE_ONLY || mode==ASSEMBLE_ONLY)
    {
      // output an object file for every source file

      // "compile" functions
      convert_symbols(compiled_functions);

      std::string cfn;
      
      if(output_file_object=="")
        cfn=get_base_name(file_name) + "." + object_file_extension;
      else
        cfn=output_file_object;

      if(write_object_file(cfn, symbol_table, compiled_functions))
        return true;

      symbol_table.clear(); // clean symbol table for next source file.
      compiled_functions.clear();
    }
  }
  
  return false;
}

/*******************************************************************\

Function: compilet::parse

  Inputs: file_name

 Outputs: true on error, false otherwise

 Purpose: parses a source file (low-level parsing)

\*******************************************************************/

bool compilet::parse(const std::string &file_name)
{
  if(file_name=="-") return parse_stdin();

  #ifdef _MSC_VER
  std::ifstream infile(widen(file_name).c_str());
  #else
  std::ifstream infile(file_name.c_str());
  #endif

  if(!infile)
  {
    error("failed to open input file", file_name);
    return true;
  }

  languaget *languagep;
  
  // Using '-x', the type of a file can be overridden;
  // otherwise, it's guessed from the extension.
  
  if(override_language!="")
  {
    if(override_language=="c++" || override_language=="c++-header")
      languagep=get_language_from_mode("cpp");
    else
      languagep=get_language_from_mode("C");
  }
  else
    languagep=get_language_from_filename(file_name);

  if(languagep==NULL)
  {
    error("failed to figure out type of file", file_name);
    return true;
  }

  languaget &language=*languagep;
  language_filet language_file;

  std::pair<language_filest::filemapt::iterator, bool>
  res=language_files.filemap.insert(
    std::pair<std::string, language_filet>(file_name, language_file));

  language_filet &lf=res.first->second;
  lf.filename=file_name;
  lf.language=languagep;

  if(mode==PREPROCESS_ONLY)
  {
    print(8, "Preprocessing: "+file_name);

    std::ostream *os = &std::cout;
    std::ofstream ofs;

    if(cmdline.isset('o'))
    {
      ofs.open(cmdline.getval('o'));
      os = &ofs;

      if(!ofs.is_open())
      {
        error(std::string("failed to open output file `")+
              cmdline.getval('o')+"'");
        return true;
      }
    }

    language.preprocess(infile, file_name, *os, get_message_handler());
  }
  else
  {
    print(8, "Parsing: "+file_name);

    if(language.parse(infile, file_name, get_message_handler()))
    {
      if(get_ui()==ui_message_handlert::PLAIN)
        error("PARSING ERROR");
      return true;
    }
  }

  lf.get_modules();
  return false;
}

/*******************************************************************\

Function: compilet::parse_stdin

  Inputs: file_name

 Outputs: true on error, false otherwise

 Purpose: parses a source file (low-level parsing)

\*******************************************************************/

bool compilet::parse_stdin()
{
  ansi_c_languaget language;

  print(8, "Parsing: (stdin)");

  if(mode==PREPROCESS_ONLY)
  {
    std::ostream *os = &std::cout;
    std::ofstream ofs;

    if(cmdline.isset('o'))
    {
      ofs.open(cmdline.getval('o'));
      os = &ofs;

      if(!ofs.is_open())
      {
        error(std::string("failed to open output file `")+
              cmdline.getval('o'));
        return true;
      }
    }

    language.preprocess(std::cin, "", *os, get_message_handler());
  }
  else
  {
    if(language.parse(std::cin, "", get_message_handler()))
    {
      if(get_ui()==ui_message_handlert::PLAIN)
        error("PARSING ERROR");
      return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: compilet::write_object_file

  Inputs: file_name, functions table

 Outputs: true on error, false otherwise

 Purpose: writes the goto functions in the function table to a
          binary format object file.

\*******************************************************************/

bool compilet::write_object_file(
  const std::string &file_name,
  const symbol_tablet &lsymbol_table,
  goto_functionst &functions)
{
  return write_bin_object_file(file_name, lsymbol_table, functions);
}

/*******************************************************************\

Function: compilet::write_bin_object_file

  Inputs: file_name, functions table

 Outputs: true on error, false otherwise

 Purpose: writes the goto functions in the function table to a
          binary format object file.

\*******************************************************************/

bool compilet::write_bin_object_file(
  const std::string &file_name,
  const symbol_tablet &lsymbol_table,
  goto_functionst &functions)
{
  print(8, "Writing binary format object `" + file_name + "'");

  // symbols
  print(8, "Symbols in table: "+
           i2string((unsigned long)lsymbol_table.symbols.size()));

  std::ofstream outfile(file_name.c_str(), std::ios::binary);

  if(!outfile.is_open())
  {
    error("Error opening file `"+file_name+"'");
    return true;
  }

  if(write_goto_binary(outfile, lsymbol_table, functions))
    return true;

  unsigned cnt=function_body_count(functions);

  debug("Functions: "+i2string(functions.function_map.size())+"; "+
        i2string(cnt)+" have a body.");

  outfile.close();

  return false;
}

/*******************************************************************\

Function: compilet::parse_source

  Inputs: file_name

 Outputs: true on error, false otherwise

 Purpose: parses a source file

\*******************************************************************/

bool compilet::parse_source(const std::string &file_name)
{
  if(parse(file_name))
    return true;
    
  if(typecheck()) // we just want to typecheck this one file here
    return true;
    
  // so we remove it from the list afterwards
  language_files.filemap.erase(file_name);
  return false;
}

/*******************************************************************\

Function: compilet::read_object

  Inputs: a file_name

 Outputs: true on error, false otherwise

 Purpose: reads an object file

\*******************************************************************/

bool compilet::read_object(
  const std::string &file_name,
  goto_functionst &functions)
{
  print(8, "Reading: " + file_name);

  // we read into a temporary symbol_table
  symbol_tablet temp_symbol_table;
  goto_functionst temp_functions;

  if(read_goto_binary(file_name, temp_symbol_table, temp_functions, *message_handler))
    return true;
  
  std::set<irep_idt> seen_modes;

  for(symbol_tablet::symbolst::const_iterator
      it=temp_symbol_table.symbols.begin();
      it!=temp_symbol_table.symbols.end();
      it++)
  {
    if(it->second.mode!="")
      seen_modes.insert(it->second.mode);
  }
  
  seen_modes.erase(ID_cpp);
  seen_modes.erase(ID_C);

  if(seen_modes.size()!=0)
  {
    error("Multi-language linking not supported");
    return true;
  }

  // hardwired to C-style linking

  linkingt linking(symbol_table, temp_symbol_table, ui_message_handler);
  
  linking.set_verbosity(verbosity);

  if(linking.typecheck_main())
    return true;
    
  if(link_functions(symbol_table, functions,
                    temp_symbol_table, temp_functions,
                    linking.replace_symbol))
    return true;

  return false;
}

/*******************************************************************\

Function: compilet::compilet

  Inputs: none

 Outputs: nothing

 Purpose: constructor

\*******************************************************************/

compilet::compilet(cmdlinet &_cmdline):
  language_uit("goto-cc " GOTOCC_VERSION, _cmdline),
  ns(symbol_table),
  cmdline(_cmdline)
{
  mode=COMPILE_LINK_EXECUTABLE;
  echo_file_name=false;
  working_directory=get_current_working_directory();
}

/*******************************************************************\

Function: compilet::~compilet

  Inputs: none

 Outputs: nothing

 Purpose: cleans up temporary files

\*******************************************************************/

compilet::~compilet()
{
  // clean up temp dirs

  for(std::list<std::string>::const_iterator it = tmp_dirs.begin();
      it!=tmp_dirs.end();
      it++)
    delete_directory(*it);
}

/*******************************************************************\

Function: compilet::function_body_count

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned compilet::function_body_count(const goto_functionst &functions)
{
  int fbs=0;

  for(goto_functionst::function_mapt::const_iterator it=
      functions.function_map.begin();
      it != functions.function_map.end();
      it++)
    if(it->second.body_available)
      fbs++;

  return fbs;
}

/*******************************************************************\

Function: compilet::link_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool compilet::link_functions(
  symbol_tablet &dest_symbol_table,
  goto_functionst &dest_functions,
  symbol_tablet &src_symbol_table,
  goto_functionst &src_functions,
  const replace_symbolt &replace_symbol)
{
  // merge functions
  Forall_goto_functions(src_it, src_functions)
  {
    // the function might have been renamed    
    replace_symbolt::expr_mapt::const_iterator e_it=
      replace_symbol.expr_map.find(src_it->first);
    irep_idt final_id=src_it->first;
    if(e_it!=replace_symbol.expr_map.end())
    {
      const exprt &rep_exp=e_it->second;
      if(rep_exp.id()==ID_symbol)
        final_id=rep_exp.get(ID_identifier);
    }
  
    // already there?
    goto_functionst::function_mapt::iterator dest_f_it=
      dest_functions.function_map.find(final_id);

    if(dest_f_it==dest_functions.function_map.end()) // not there yet
    {
      replace_symbols_in_function(src_it->second, replace_symbol);

      goto_functionst::goto_functiont &in_dest_symbol_table=
        dest_functions.function_map[final_id];

      in_dest_symbol_table.body.swap(src_it->second.body);
      in_dest_symbol_table.body_available=src_it->second.body_available;
      in_dest_symbol_table.type=src_it->second.type;
    }
    else // collision!
    {
      goto_functionst::goto_functiont &in_dest_symbol_table=
        dest_functions.function_map[final_id];

      goto_functionst::goto_functiont &src_func=src_it->second;

      if(in_dest_symbol_table.body.instructions.empty())
      {
        // the one with body wins!
        replace_symbols_in_function(src_func, replace_symbol);
        
        in_dest_symbol_table.body.swap(src_func.body);
        in_dest_symbol_table.body_available=src_func.body_available;
        in_dest_symbol_table.type=src_func.type;
      }
      else if(src_func.body.instructions.empty())
      {
        // just keep the old one in dest
      }
      else if(in_dest_symbol_table.type.get_bool(ID_C_inlined))
      {
        // ok, we silently ignore
      }
      else if(base_type_eq(in_dest_symbol_table.type, src_func.type, ns))
      {
        // keep the one in in_symbol_table -- libraries come last!
        std::stringstream str;
        str << "warning: function `" << final_id << "' in module `"
            << src_symbol_table.symbols.begin()->second.module
            << "' is shadowed by a definition in module `"
            << symbol_table.symbols.begin()->second.module << "'";
        warning(str.str());
      }
      else
      {
        std::stringstream str;
        str << "error: duplicate definition of function `"
            << final_id
            << "'" << std::endl;
        str << "In module `" 
            << symbol_table.symbols.begin()->second.module
            << "' and module `"
            << src_symbol_table.symbols.begin()->second.module << "'";
        error(str.str());
        return true;
      }
    }
  }

  return false;
}

/*******************************************************************\

Function: compilet::replace_symbols_in_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compilet::replace_symbols_in_function(
  goto_functionst::goto_functiont &function,
  const replace_symbolt &replace_symbol) const
{
  goto_programt &program=function.body;
  replace_symbol.replace(function.type);

  Forall_goto_program_instructions(iit, program)
  {
    replace_symbol.replace(iit->code);
    replace_symbol.replace(iit->guard);
  }
}

/*******************************************************************\

Function: compilet::add_compiler_specific_defines

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compilet::add_compiler_specific_defines(configt &config) const
{
  config.ansi_c.defines.push_back("__GOTO_CC_VERSION__=" GOTOCC_VERSION);
}

/*******************************************************************\

Function: compilet::convert_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compilet::convert_symbols(goto_functionst &dest)
{
  goto_convert_functionst converter(symbol_table, dest, ui_message_handler);

  // the compilation may add symbols!

  symbol_tablet::symbolst::size_type before=0;
  
  while(before!=symbol_table.symbols.size())
  {
    before=symbol_table.symbols.size();

    typedef std::set<irep_idt> symbols_sett;
    symbols_sett symbols;
  
    Forall_symbols(it, symbol_table.symbols)
      symbols.insert(it->first);

    // the symbol table itertors aren't stable
    for(symbols_sett::const_iterator
        it=symbols.begin();
        it!=symbols.end();
        ++it)
    {
      symbol_tablet::symbolst::iterator s_it=symbol_table.symbols.find(*it);
      assert(s_it!=symbol_table.symbols.end());

      if(s_it->second.type.id()==ID_code &&
          s_it->second.value.id()!="compiled" &&
          s_it->second.value.is_not_nil())
      {
        print(9, "Compiling "+id2string(s_it->first));
        converter.convert_function(s_it->first);
        s_it->second.value=exprt("compiled");
      }
    }
  }
}
