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
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/link_to_library.h>

#include <analyses/is_threaded.h>
#include <analyses/goto_check.h>
#include <analyses/local_may_alias.h>

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
#include "static_show_domain.h"
#include "static_simplifier.h"

/*******************************************************************\

Function: goto_analyzer_parse_optionst::goto_analyzer_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_analyzer_parse_optionst::goto_analyzer_parse_optionst(int argc, const char **argv):
  parse_options_baset(GOTO_ANALYSER_OPTIONS, argc, argv),
  language_uit(cmdline, ui_message_handler),
  ui_message_handler(cmdline, "GOTO-ANALYZER " CBMC_VERSION)
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

  
  // Output format choice
  options.set_option("text", false);
  options.set_option("json", false);
  options.set_option("xml", false);
  options.set_option("dot", false);
  options.set_option("outfile", "-");
  
  if (cmdline.isset("text"))
  {
    options.set_option("text", true);
    options.set_option("outfile", cmdline.get_value("text"));  
  }
  else if (cmdline.isset("json"))
  {
    options.set_option("json", true);
    options.set_option("outfile", cmdline.get_value("json"));
  }
  else if (cmdline.isset("xml"))
  {
    options.set_option("xml", true);
    options.set_option("outfile", cmdline.get_value("xml"));
  }
  else if (cmdline.isset("dot"))
  {
    options.set_option("dot", true);
    options.set_option("outfile", cmdline.get_value("dot"));
  }
  else
  {
    options.set_option("text", true);
  }

  
  // Task options
  options.set_option(    "show", false);
  options.set_option(  "verify", false);
  options.set_option("simplify", false);

  if (cmdline.isset("show") ||
      cmdline.isset("show-intervals") ||
      cmdline.isset("show-non-null"))
    options.set_option("show", true);
  else if (cmdline.isset("verify"))
    options.set_option("verify", true);
  else if (cmdline.isset("simplify"))
  {
    options.set_option("simplify", true);
    options.set_option("outfile", cmdline.get_value("simplify"));
  }

  if (!(options.get_bool_option("show")  ||
	options.get_bool_option("verify")  ||
	options.get_bool_option("simplify")))
  {
    status() << "Task defaults to --show" << eom;
    options.set_option("show", true);
  }

  
  // Abstract interpreter choice
  options.set_option("flow-sensitive", false);
  options.set_option("concurrent", false);

  if (cmdline.isset("flow-sensitive"))
    options.set_option("flow-sensitive", true);
  else if (cmdline.isset("concurrent"))
    options.set_option("concurrent", true);
  else
  {
    is_threadedt is_threaded(goto_model.goto_functions);
    bool contains_concurrent_code = is_threaded();

    options.set_option("flow-sensitive", !contains_concurrent_code);
    options.set_option("concurrent",  contains_concurrent_code);
  }

  
  // Domain choice
  options.set_option("constants", false);
  options.set_option("intervals", false);
  options.set_option("non-null", false);
  options.set_option("dependence-graph", false);

  if (cmdline.isset("intervals") ||
      cmdline.isset("show-intervals")) 
    options.set_option("intervals", true);
  else if (cmdline.isset("non-null") ||
      cmdline.isset("show-non-null")) 
    options.set_option("non-null", true);
  else if (cmdline.isset("constants"))
    options.set_option("constants", true);
  else if (cmdline.isset("dependence-graph"))
    options.set_option("dependence-graph", true);
    
  if (!(options.get_bool_option("constants")  ||
	options.get_bool_option("intervals")  ||
	options.get_bool_option("non-null") ||
	options.get_bool_option("dependence-graph")))
  {
    status() << "Domain defaults to --constants" << eom;
    options.set_option("constants", true);
  }
  
}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int goto_analyzer_parse_optionst::doit()
{
  try
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
    
    goto_model.set_message_handler(get_message_handler());
    
    if(goto_model(cmdline.args))
      return 6;
    
    if(process_goto_program(options))
      return 6;

    if(cmdline.isset("taint"))
    {
      std::string taint_file=cmdline.get_value("taint");

      if(cmdline.isset("show-taint"))
      {
	taint_analysis(goto_model, taint_file, get_message_handler(), true, "");
	return 0;
      }
      else
      {
	std::string json_file=cmdline.get_value("json");
	bool result=
	  taint_analysis(goto_model, taint_file, get_message_handler(), false, json_file);
	return result?10:0;
      }
    }

    if(cmdline.isset("unreachable-instructions"))
    {
      const std::string json_file=cmdline.get_value("json");

      if(json_file.empty())
	unreachable_instructions(goto_model, false, std::cout);
      else if(json_file=="-")
	unreachable_instructions(goto_model, true, std::cout);
      else
      {
	std::ofstream ofs(json_file);
	if(!ofs)
	{
	  error() << "Failed to open json output `"
		  << json_file << "'" << eom;
	  return 6;
	}
	
	unreachable_instructions(goto_model, true, ofs);
      }

      return 0;
    }

    if(cmdline.isset("show-local-may-alias"))
    {
      namespacet ns(goto_model.symbol_table);
  
      forall_goto_functions(it, goto_model.goto_functions)
      {
	std::cout << ">>>>\n";
	std::cout << ">>>> " << it->first << '\n';
	std::cout << ">>>>\n";
	local_may_aliast local_may_alias(it->second);
	local_may_alias.output(std::cout, it->second, ns);
	std::cout << '\n';
      }

      return 0;
    }

    label_properties(goto_model);

    if(cmdline.isset("show-properties"))
    {
      show_properties(goto_model, get_ui());
      return 0;
    }

    if(set_properties())
      return 7;
  
    
    // Output file factory
    std::ostream *out;
    const std::string outfile = options.get_option("outfile");
    if (outfile == "-")
      out = &std::cout;
    else
    {
      out = new std::ofstream(outfile);
      if(!*out)
      {
	error() << "Failed to open output file `"
		<< outfile << "'" << eom;
	return 6;
      }
    }


    // Run the analysis
    bool result = true;
    if (options.get_bool_option("show"))
      result = static_show_domain(goto_model, options, get_message_handler(), *out);
    
    else if (options.get_bool_option("verify"))
      result =    static_analyzer(goto_model, options, get_message_handler(), *out);
    
    else if (options.get_bool_option("simplify"))
      result =  static_simplifier(goto_model, options, get_message_handler(), *out);
    else
    {
      error() << "No task given" << eom;
      return 6;
    }
  
    if (out != &std::cout)
      delete out;
  
  return result?10:0;
  
  // Final defensive error case
  error() << "no analysis option given -- consider reading --help"
          << eom;
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
  
  catch(int x)
  {
    return x;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return 6;
  }

}

/*******************************************************************\

Function: goto_analyzer_parse_optionst::set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_analyzer_parse_optionst::set_properties()
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_model, cmdline.get_values("property"));
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

Function: goto_analyzer_parse_optionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool goto_analyzer_parse_optionst::process_goto_program(
  const optionst &options)
{
  try
  {
    #if 0
    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(goto_model);

    // add the library
    status() << "Adding CPROVER library (" 
             << config.ansi_c.arch << ")" << eom;
    link_to_library(goto_model, ui_message_handler);
    #endif

    // remove function pointers
    status() << "Removing function pointers and virtual functions" << eom;
    remove_function_pointers(goto_model, cmdline.isset("pointer-check"));
    remove_virtual_functions(goto_model);

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_model, ui_message_handler);
    
    // remove returns, gcc vectors, complex
    remove_returns(goto_model);
    remove_vector(goto_model);
    remove_complex(goto_model);

    #if 0
    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);
    #endif
    
    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();
    
    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      namespacet ns(goto_model.symbol_table);

      goto_model.goto_functions.output(ns, std::cout);
      return true;
    }

    // show it?
    if(cmdline.isset("show-symbol-table"))
    {
      ::show_symbol_table(goto_model, get_ui());
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
    "Task options:\n"
    " --show                       run abstract interpreter and display domains\n"
    " --verify                     run abstract interpreter and check assertions\n"
    " --simplify file_name         run abstract interpreter and simplify program\n"
    "\n"
    "Abstract interpreter options:\n"
    " --flow-sensitive             use flow-sensitive abstract interpreter\n"
    " --concurrent                 use concurrent abstract interpreter\n"
    "\n"
    "Domain options:\n"
    " --constants                  constant abstraction\n"
    " --intervals                  interval abstraction\n"
    " --non-null                   non-null abstraction\n"
    " --dependence-graph           dependency relation between instructions\n"
    "\n"
    "Output options:\n"
    " --text file_name             output results in plain text to given file\n"
    " --json file_name             output results in JSON format to given file\n"
    " --xml file_name              output results in XML format to given file\n"
    " --dot file_name              output results in DOT format to given file\n"
    "\n"
    "Other analyses:\n"
    " --taint file_name            perform taint analysis using rules in given file\n"
    " --unreachable-instructions   list dead code\n"
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
