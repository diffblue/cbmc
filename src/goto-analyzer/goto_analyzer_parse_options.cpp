/*******************************************************************\

Module: Goto-Analyser Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib> // exit()
#include <iostream>
#include <fstream>
#include <memory>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <java_bytecode/java_bytecode_language.h>
#include <jsil/jsil_language.h>

#include <goto-programs/set_properties.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/link_to_library.h>

#include <analyses/goto_check.h>

#include <langapi/mode.h>

#include <util/language.h>
#include <util/options.h>
#include <util/config.h>
#include <util/string2int.h>
#include <util/unicode.h>

#include <cbmc/version.h>

#include "goto_analyzer_parse_options.h"
#include "taint_analysis.h"
#include "unreachable_instructions.h"
#include "static_analyzer.h"

/*******************************************************************\

Function: goto_analyzer_parse_optionst::goto_analyzer_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_analyzer_parse_optionst::goto_analyzer_parse_optionst(int argc, const char **argv):
  parse_options_baset(GOTO_ANALYSER_OPTIONS, argc, argv),
  language_uit("GOTO-ANALYSER " CBMC_VERSION, cmdline)
{
}
  
/*******************************************************************\

Function: goto_analyzer_parse_optionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_analyzer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
  register_language(new_java_bytecode_language);
  register_language(new_jsil_language);
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_analyzer_parse_optionst::eval_verbosity()
{
  // this is our default verbosity
  unsigned int v=messaget::M_STATISTICS;
  
  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2unsigned(cmdline.get_value("verbosity"));
    if(v>10) v=10;
  }
  
  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_analyzer_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  #if 0
  if(cmdline.isset("c89"))
    config.ansi_c.set_c89();

  if(cmdline.isset("c99"))
    config.ansi_c.set_c99();

  if(cmdline.isset("c11"))
    config.ansi_c.set_c11();

  if(cmdline.isset("cpp98"))
    config.cpp.set_cpp98();

  if(cmdline.isset("cpp03"))
    config.cpp.set_cpp03();

  if(cmdline.isset("cpp11"))
    config.cpp.set_cpp11();
  #endif

  #if 0
  // check array bounds
  if(cmdline.isset("bounds-check"))
    options.set_option("bounds-check", true);
  else
    options.set_option("bounds-check", false);

  // check division by zero
  if(cmdline.isset("div-by-zero-check"))
    options.set_option("div-by-zero-check", true);
  else
    options.set_option("div-by-zero-check", false);

  // check overflow/underflow
  if(cmdline.isset("signed-overflow-check"))
    options.set_option("signed-overflow-check", true);
  else
    options.set_option("signed-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("unsigned-overflow-check"))
    options.set_option("unsigned-overflow-check", true);
  else
    options.set_option("unsigned-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("float-overflow-check"))
    options.set_option("float-overflow-check", true);
  else
    options.set_option("float-overflow-check", false);

  // check for NaN (not a number)
  if(cmdline.isset("nan-check"))
    options.set_option("nan-check", true);
  else
    options.set_option("nan-check", false);

  // check pointers
  if(cmdline.isset("pointer-check"))
    options.set_option("pointer-check", true);
  else
    options.set_option("pointer-check", false);

  // check for memory leaks
  if(cmdline.isset("memory-leak-check"))
    options.set_option("memory-leak-check", true);
  else
    options.set_option("memory-leak-check", false);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_values("error-label"));
  #endif
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int goto_analyzer_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }
  
  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);
  eval_verbosity();

  //
  // Print a banner
  //
  status() << "GOTO-ANALYSER version " CBMC_VERSION " "
           << sizeof(void *)*8 << "-bit "
           << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  register_languages();
  const namespacet ns(symbol_table);
  
  goto_functionst goto_functions;

  int get_goto_program_ret=
    get_goto_program(options, goto_functions);

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  if(cmdline.isset("taint"))
  {
    std::string taint_file=cmdline.get_value("taint");

    if(cmdline.isset("show-taint"))
    {
      taint_analysis(goto_functions, ns, taint_file, get_message_handler(), true, "");
      return 0;
    }
    else
    {
      std::string json_file=cmdline.get_value("json");
      bool result=
        taint_analysis(goto_functions, ns, taint_file, get_message_handler(), false, json_file);
      return result?10:0;
    }
  }

  if(cmdline.isset("unreachable-instructions"))
  {
    const std::string json_file=cmdline.get_value("json");

    if(json_file.empty())
      unreachable_instructions(goto_functions, ns, false, std::cout);
    else if(json_file=="-")
      unreachable_instructions(goto_functions, ns, true, std::cout);
    else
    {
      std::ofstream ofs(json_file);
      if(!ofs)
      {
        error() << "Failed to open json output `"
                << json_file << "'" << eom;
        return 6;
      }

      unreachable_instructions(goto_functions, ns, true, ofs);
    }

    return 0;
  }

  label_properties(goto_functions);

  if(cmdline.isset("show-properties"))
  {
    const namespacet ns(symbol_table);
    show_properties(ns, get_ui(), goto_functions);
    return 0;
  }

  if(set_properties(goto_functions))
    return 7;
  
  if(cmdline.isset("show-intervals"))
  {
    show_intervals(goto_functions, ns, std::cout);
    return 0;
  }

  if(cmdline.isset("non-null") ||
     cmdline.isset("intervals"))
  {
    optionst options;
    options.set_option("json", cmdline.get_value("json"));
    options.set_option("xml", cmdline.get_value("xml"));
    bool result=
      static_analyzer(goto_functions, ns, options, get_message_handler());
    return result?10:0;
  }

  error() << "no analysis option given -- consider reading --help"
          << eom;
  return 6;
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_analyzer_parse_optionst::set_properties(goto_functionst &goto_functions)
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_functions, cmdline.get_values("property"));
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
int goto_analyzer_parse_optionst::get_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  if(cmdline.args.empty())
  {
    error() << "Please provide a program to verify" << eom;
    return 6;
  }
  
  try
  {
    if(cmdline.isset("show-parse-tree"))
    {
      if(cmdline.args.size()!=1 ||
         is_goto_binary(cmdline.args[0]))
      {
        error() << "Please give exactly one source file" << eom;
        return 6;
      }
      
      std::string filename=cmdline.args[0];
      
      #ifdef _MSC_VER
      std::ifstream infile(widen(filename).c_str());
      #else
      std::ifstream infile(filename.c_str());
      #endif
                
      if(!infile)
      {
        error() << "failed to open input file `" << filename << "'" << eom;
        return 6;
      }
                              
      languaget *language=get_language_from_filename(filename);
      
      if(language==NULL)
      {
        error() << "failed to figure out type of file `" <<  filename << "'" << eom;
        return 6;
      }
      
      language->set_message_handler(get_message_handler());
                                                                
      status("Parsing", filename);
  
      if(language->parse(infile, filename))
      {
        error() << "PARSING ERROR" << eom;
        return 6;
      }
      
      language->show_parse(std::cout);
      return 0;
    }

    cmdlinet::argst binaries;
    binaries.reserve(cmdline.args.size());

    for(cmdlinet::argst::iterator
        it=cmdline.args.begin();
        it!=cmdline.args.end();
        ) // no ++it
    {
      if(is_goto_binary(*it))
      {
        binaries.push_back(*it);
        it=cmdline.args.erase(it);
        continue;
      }

      ++it;
    }

    if(!cmdline.args.empty())
    {
      if(parse()) return 6;
      if(typecheck()) return 6;
      if(final()) return 6;

      // we no longer need any parse trees or language files
      clear_parse();
    }

    for(cmdlinet::argst::const_iterator
        it=binaries.begin();
        it!=binaries.end();
        ++it)
    {
      status() << "Reading GOTO program from file " << eom;

      if(read_object_and_link(*it, symbol_table, goto_functions, *this))
        return 6;
    }

    if(!binaries.empty())
      config.set_from_symbol_table(symbol_table);

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table();
      return 0;
    }

    status() << "Generating GOTO Program" << eom;

    goto_convert(symbol_table, goto_functions, ui_message_handler);

    if(process_goto_program(options, goto_functions))
      return 6;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 6;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return 6;
  }
  
  catch(int)
  {
    return 6;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return 6;
  }
  
  return -1; // no error, continue
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool goto_analyzer_parse_optionst::process_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  try
  {
    namespacet ns(symbol_table);

    #if 0
    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(symbol_table, goto_functions);

    // add the library
    status() << "Adding CPROVER library (" 
             << config.ansi_c.arch << ")" << eom;
    link_to_library(symbol_table, goto_functions, ui_message_handler);
    #endif

    // remove function pointers
    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(symbol_table, goto_functions,
      cmdline.isset("pointer-check"));

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);
    
    // remove returns, gcc vectors, complex
    remove_returns(symbol_table, goto_functions);
    remove_vector(symbol_table, goto_functions);
    remove_complex(symbol_table, goto_functions);

    #if 0
    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(ns, options, goto_functions);
    #endif
    
    // recalculate numbers, etc.
    goto_functions.update();

    // add loop ids
    goto_functions.compute_loop_numbers();
    
    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      goto_functions.output(ns, std::cout);
      return true;
    }
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void goto_analyzer_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* * GOTO-ANALYSER " CBMC_VERSION " - Copyright (C) 2016 ";
    
  std::cout << "(" << (sizeof(void *)*8) << "-bit version)";
    
  std::cout << " * *\n";
    
  std::cout <<
    "* *                Daniel Kroening, DiffBlue                * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-analyzer [-h] [--help]  show help\n"
    " goto-analyzer file.c ...     source file names\n"
    "\n"
    "Analyses:\n"
    "\n"
    " --taint file_name            perform taint analysis using rules in given file\n"
    " --unreachable-instructions   list dead code\n"
    " --interval                   interval analysis\n"
    " --non-null                   non-null analysis\n"
    "\n"
    "Analysis options:\n"
    " --json file_name             output results in JSON format to given file\n"
    " --xml file_name              output results in XML format to given file\n"
    "\n"
    "C/C++ frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --arch X                     set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    " --c89/99/11                  set C language standard (default: "
                                   << (configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C89?"c89":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C99?"c99":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C11?"c11":"") << ")\n"
    " --cpp98/03/11                set C++ language standard (default: "
                                   << (configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP98?"cpp98":
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP03?"cpp03":
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP11?"cpp11":"") << ")\n"
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-library                 disable built-in abstract C library\n"
    "\n"
    "Java Bytecode frontend options:\n"
    " --classpath dir/jar          set the classpath\n"
    " --main-class class-name      set the name of the main class\n"
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    " --show-properties            show the properties, but don't run analysis\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    "\n";
}
