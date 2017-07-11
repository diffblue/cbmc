/*******************************************************************\

Module: Symex Command Line Options Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symex Command Line Options Processing

#include "clobber_parse_options.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

#include <util/string2int.h>
#include <util/config.h>
#include <util/language.h>
#include <util/options.h>
#include <util/memory_info.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/xml_goto_trace.h>

#include <goto-instrument/dump_c.h>

#include <langapi/mode.h>

#include <cbmc/version.h>

// #include "clobber_instrumenter.h"

clobber_parse_optionst::clobber_parse_optionst(int argc, const char **argv):
  parse_options_baset(CLOBBER_OPTIONS, argc, argv),
  language_uit(cmdline, ui_message_handler),
  ui_message_handler(cmdline, "CLOBBER " CBMC_VERSION)
{
}

void clobber_parse_optionst::eval_verbosity()
{
  // this is our default verbosity
  int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2int(cmdline.get_value("verbosity"));
    if(v<0)
      v=0;
    else if(v>10)
      v=10;
  }

  ui_message_handler.set_verbosity(v);
}

void clobber_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

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
    options.set_option("error-label", cmdline.get_value("error-label"));
}

/// invoke main modules
int clobber_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return 0;
  }

  register_language(new_ansi_c_language);
  register_language(new_cpp_language);

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity();

  goto_functionst goto_functions;

  try
  {
    if(get_goto_program(options, goto_functions))
      return 6;

    label_properties(goto_functions);

    if(cmdline.isset("show-properties"))
    {
      const namespacet ns(symbol_table);
      show_properties(ns, get_ui(), goto_functions);
      return 0;
    }

    set_properties(goto_functions);

    // do instrumentation

    const namespacet ns(symbol_table);

    std::ofstream out("simulator.c");

    if(!out)
      throw std::string("failed to create file simulator.c");

    dump_c(goto_functions, true, false, ns, out);

    status() << "instrumentation complete; compile and execute simulator.c"
             << eom;

    return 0;
  }

  catch(const std::string error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

  catch(const char *error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << messaget::eom;
    return 8;
  }

  #if 0
  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;
  #endif
}

bool clobber_parse_optionst::set_properties(goto_functionst &goto_functions)
{
  if(cmdline.isset("property"))
    ::set_properties(goto_functions, cmdline.get_values("property"));

  return false;
}

bool clobber_parse_optionst::get_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  if(cmdline.args.empty())
  {
    error() << "Please provide a program to verify" << eom;
    return true;
  }

  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status() << "Reading GOTO program from file" << eom;

      if(read_goto_binary(cmdline.args[0],
           symbol_table, goto_functions, get_message_handler()))
        return true;

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

      irep_idt entry_point=goto_functions.entry_point();

      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "The goto binary has no entry point; please complete linking"
                << eom;
        return true;
      }
    }
    else if(cmdline.isset("show-parse-tree"))
    {
      if(cmdline.args.size()!=1)
      {
        error() << "Please give one source file only" << eom;
        return true;
      }

      std::string filename=cmdline.args[0];

      #ifdef _MSC_VER
      std::ifstream infile(widen(filename));
      #else
      std::ifstream infile(filename);
      #endif

      if(!infile)
      {
        error() << "failed to open input file `" << filename << "'" << eom;
        return true;
      }

      languaget *language=get_language_from_filename(filename);
      language->get_language_options(cmdline);

      if(language==nullptr)
      {
        error() << "failed to figure out type of file `" <<  filename << "'"
                << eom;
        return true;
      }

      language->set_message_handler(get_message_handler());

      status() << "Parsing " << filename << eom;

      if(language->parse(infile, filename))
      {
        error() << "PARSING ERROR" << eom;
        return true;
      }

      language->show_parse(std::cout);
      return true;
    }
    else
    {
      if(parse() ||
         typecheck() ||
         final())
        return true;

      // we no longer need any parse trees or language files
      clear_parse();

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

      irep_idt entry_point=goto_functions.entry_point();

      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "No entry point; please provide a main function" << eom;
        return true;
      }

      status() << "Generating GOTO Program" << eom;

      goto_convert(symbol_table, goto_functions, ui_message_handler);
    }

    // finally add the library
    #if 0
    link_to_library(symbol_table, goto_functions, ui_message_handler);
    #endif

    if(process_goto_program(options, goto_functions))
      return true;
  }

  return false;
}

bool clobber_parse_optionst::process_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  {
    namespacet ns(symbol_table);

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(ns, options, goto_functions);

    // recalculate numbers, etc.
    goto_functions.update();

    // add loop ids
    goto_functions.compute_loop_numbers();

    // if we aim to cover, replace
    // all assertions by false to prevent simplification

    if(cmdline.isset("cover-assertions"))
      make_assertions_false(goto_functions);

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_functions);
      return true;
    }

    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      show_goto_functions(ns, get_ui(), goto_functions);
      return true;
    }
  }

  return false;
}

#if 0
void clobber_parse_optionst::report_properties(
  const path_searcht::property_mapt &property_map)
{
  for(const auto &prop_pair : property_map)
  {
    if(get_ui()==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(prop_pair.first));

      std::string status_string;

      switch(prop_pair.second.status)
      {
      case path_searcht::PASS: status_string="OK"; break;
      case path_searcht::FAIL: status_string="FAILURE"; break;
      case path_searcht::NOT_REACHED: status_string="OK"; break;
      }

      xml_result.set_attribute("status", status_string);

      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << prop_pair.first << "] "
               << prop_pair.second.description << ": ";
      switch(prop_pair.second.status)
      {
      case path_searcht::PASS: status() << "OK"; break;
      case path_searcht::FAIL: status() << "FAILED"; break;
      case path_searcht::NOT_REACHED: status() << "OK"; break;
      }
      status() << eom;
    }

    if(cmdline.isset("show-trace") &&
       prop_pair.second.status==path_searcht::FAIL)
      show_counterexample(prop_pair.second.error_trace);
  }

  if(!cmdline.isset("property"))
  {
    status() << eom;

    unsigned failed=0;

    for(const auto &prop_pair : property_map)
      if(prop_pair.second.status==path_searcht::FAIL)
        failed++;

    status() << "** " << failed
             << " of " << property_map.size() << " failed"
             << eom;
  }
}
#endif

void clobber_parse_optionst::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << '\n';
    }
    break;

  default:
    assert(false);
  }
}

void clobber_parse_optionst::show_counterexample(
  const goto_tracet &error_trace)
{
  const namespacet ns(symbol_table);

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    std::cout << "\nCounterexample:\n";
    show_goto_trace(std::cout, ns, error_trace);
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(ns, error_trace, xml);
      std::cout << xml << '\n';
    }
    break;

  default:
    assert(false);
  }
}

void clobber_parse_optionst::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << '\n';
    }
    break;

  default:
    assert(false);
  }
}

/// display command line help
void clobber_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *     CLOBBER " CBMC_VERSION " - Copyright (C) 2014 ";

  std::cout << "(" << (sizeof(void *)*8) << "-bit version)";

  std::cout << "     * *\n";

  std::cout <<
    "* *                    Daniel Kroening                      * *\n"
    "* *                 University of Oxford                    * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " symex [-?] [-h] [--help]     show help\n"
    " symex file.c ...             source file names\n"
    "\n"
    "Frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    " --ppc-macos                  set MACOS/PPC architecture\n"
    " --mm model                   set memory model (default: sc)\n"
    " --arch                       set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-arch                    don't set up an architecture\n"
    " --no-library                 disable built-in abstract C library\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --round-to-nearest           IEEE floating point rounding mode (default)\n"
    " --round-to-plus-inf          IEEE floating point rounding mode\n"
    " --round-to-minus-inf         IEEE floating point rounding mode\n"
    " --round-to-zero              IEEE floating point rounding mode\n"
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    " --show-properties            show the properties\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    "\n"
    "Symex options:\n"
    " --function name              set main function name\n"
    " --property nr                only check one specific property\n"
    " --depth nr                   limit search depth\n"
    " --context-bound nr           limit number of context switches\n"
    " --unwind nr                  unwind nr times\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
