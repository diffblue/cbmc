/*******************************************************************\

Module: Symex Command Line Options Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>
#include <cstdlib>

#include <util/string2int.h>
#include <util/config.h>
#include <util/language.h>
#include <util/options.h>
#include <util/memory_info.h>
#include <util/unicode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <java_bytecode/java_bytecode_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_virtual_functions.h>

#include <goto-instrument/cover.h>

#include <langapi/mode.h>

#include <cbmc/version.h>

#include <path-symex/locs.h>

#include "path_search.h"
#include "symex_parse_options.h"

/*******************************************************************\

Function: symex_parse_optionst::symex_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_parse_optionst::symex_parse_optionst(int argc, const char **argv):
  parse_options_baset(SYMEX_OPTIONS, argc, argv),
  language_uit(cmdline, ui_message_handler),
  ui_message_handler(cmdline, "Symex " CBMC_VERSION)
{
}

/*******************************************************************\

Function: symex_parse_optionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parse_optionst::eval_verbosity()
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

/*******************************************************************\

Function: symex_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parse_optionst::get_command_line_options(optionst &options)
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
  GOTO_CHECK_PARSE_OPTIONS(cmdline, options);

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
}

/*******************************************************************\

Function: symex_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int symex_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }

  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
  register_language(new_java_bytecode_language);

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity();

  goto_model.set_message_handler(get_message_handler());

  if(goto_model(cmdline.args))
    return 6;

  if(process_goto_program(options))
    return 6;

  label_properties(goto_model);

  if(cmdline.isset("show-properties"))
  {
    show_properties(goto_model, get_ui());
    return 0;
  }

  if(set_properties())
    return 7;

  if(cmdline.isset("show-locs"))
  {
    const namespacet ns(goto_model.symbol_table);
    locst locs(ns);
    locs.build(goto_model.goto_functions);
    locs.output(std::cout);
    return 0;
  }

  // do actual Symex

  try
  {
    const namespacet ns(goto_model.symbol_table);
    path_searcht path_search(ns);

    path_search.set_message_handler(get_message_handler());

    if(cmdline.isset("depth"))
      path_search.set_depth_limit(unsafe_string2unsigned(cmdline.get_value("depth")));

    if(cmdline.isset("context-bound"))
      path_search.set_context_bound(unsafe_string2unsigned(cmdline.get_value("context-bound")));

    if(cmdline.isset("branch-bound"))
      path_search.set_branch_bound(unsafe_string2unsigned(cmdline.get_value("branch-bound")));

    if(cmdline.isset("unwind"))
      path_search.set_unwind_limit(unsafe_string2unsigned(cmdline.get_value("unwind")));

    if(cmdline.isset("dfs"))
      path_search.set_dfs();

    if(cmdline.isset("bfs"))
      path_search.set_bfs();

    if(cmdline.isset("locs"))
      path_search.set_locs();

    if(cmdline.isset("show-vcc"))
    {
      path_search.show_vcc=true;
      path_search(goto_model.goto_functions);
      return 0;
    }

    path_search.eager_infeasibility=
      cmdline.isset("eager-infeasibility");

    if(cmdline.isset("cover"))
    {
      // test-suite generation
      path_search(goto_model.goto_functions);
      report_cover(path_search.property_map);
      return 0;
    }
    else
    {
      // do actual symex, for assertion checking
      switch(path_search(goto_model.goto_functions))
      {
      case safety_checkert::SAFE:
        report_properties(path_search.property_map);
        report_success();
        return 0;

      case safety_checkert::UNSAFE:
        report_properties(path_search.property_map);
        report_failure();
        return 10;

      default:
        return 8;
      }
    }
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

  #if 0
  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;
  #endif
}

/*******************************************************************\

Function: symex_parse_optionst::set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_parse_optionst::set_properties()
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_model.goto_functions, cmdline.get_values("property"));
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

Function: symex_parse_optionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_parse_optionst::process_goto_program(const optionst &options)
{
  try
  {
    // we add the library
    status() << "Adding CPROVER library" << eom;
    link_to_library(goto_model, ui_message_handler);

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_model, ui_message_handler);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);

    // remove stuff
    remove_complex(goto_model);
    remove_vector(goto_model);
    remove_virtual_functions(goto_model);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();

    if(cmdline.isset("cover"))
    {
      std::string criterion=cmdline.get_value("cover");

      coverage_criteriont c;

      if(criterion=="assertion" || criterion=="assertions")
        c=coverage_criteriont::ASSERTION;
      else if(criterion=="path" || criterion=="paths")
        c=coverage_criteriont::PATH;
      else if(criterion=="branch" || criterion=="branches")
        c=coverage_criteriont::BRANCH;
      else if(criterion=="location" || criterion=="locations")
        c=coverage_criteriont::LOCATION;
      else if(criterion=="decision" || criterion=="decisions")
        c=coverage_criteriont::DECISION;
      else if(criterion=="condition" || criterion=="conditions")
        c=coverage_criteriont::CONDITION;
      else if(criterion=="mcdc")
        c=coverage_criteriont::MCDC;
      else if(criterion=="cover")
        c=coverage_criteriont::COVER;
      else
      {
        error() << "unknown coverage criterion" << eom;
        return true;
      }

      status() << "Instrumenting coverge goals" << eom;
      instrument_cover_goals(symbol_table, goto_model.goto_functions, c);
      goto_model.goto_functions.update();
    }

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_model.goto_functions);
      return true;
    }

    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      show_goto_functions(goto_model, get_ui());
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

Function: symex_parse_optionst::report_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parse_optionst::report_properties(
  const path_searcht::property_mapt &property_map)
{
  if(get_ui()==ui_message_handlert::PLAIN)
    status() << "\n** Results:" << eom;

  for(path_searcht::property_mapt::const_iterator
      it=property_map.begin();
      it!=property_map.end();
      it++)
  {
    if(get_ui()==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(it->first));

      std::string status_string;

      switch(it->second.status)
      {
      case path_searcht::SUCCESS: status_string="SUCCESS"; break;
      case path_searcht::FAILURE: status_string="FAILURE"; break;
      case path_searcht::NOT_REACHED: status_string="SUCCESS"; break;
      }

      xml_result.set_attribute("status", status_string);

      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << it->first << "] "
               << it->second.description << ": ";
      switch(it->second.status)
      {
      case path_searcht::SUCCESS: status() << "SUCCESS"; break;
      case path_searcht::FAILURE: status() << "FAILURE"; break;
      case path_searcht::NOT_REACHED: status() << "SUCCESS"; break;
      }
      status() << eom;
    }

    if((cmdline.isset("show-trace") ||
        cmdline.isset("trace")) &&
       it->second.is_failure())
      show_counterexample(it->second.error_trace);
  }

  if(!cmdline.isset("property"))
  {
    status() << eom;

    unsigned failed=0;

    for(path_searcht::property_mapt::const_iterator
        it=property_map.begin();
        it!=property_map.end();
        it++)
      if(it->second.is_failure())
        failed++;

    status() << "** " << failed
             << " of " << property_map.size() << " failed"
             << eom;
  }
}

/*******************************************************************\

Function: symex_parse_optionst::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parse_optionst::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;

  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: symex_parse_optionst::show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parse_optionst::show_counterexample(
  const goto_tracet &error_trace)
{
  const namespacet ns(goto_model.symbol_table);

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    std::cout << '\n' << "Counterexample:" << '\n';
    show_goto_trace(std::cout, ns, error_trace);
    break;

  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, error_trace, xml);
      std::cout << xml << std::flush;
    }
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: symex_parse_optionst::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parse_optionst::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;

  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: symex_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void symex_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *     Symex " CBMC_VERSION " - Copyright (C) 2013 ";

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
    "Analysis options:\n"
    " --show-properties            show the properties, but don't run analysis\n"
    " --property id                only check one specific property\n"
    " --stop-on-fail               stop analysis once a failed property is detected\n"
    " --trace                      give a counterexample trace for failed properties\n"
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
    " --round-to-nearest           IEEE floating point rounding mode (default)\n"
    " --round-to-plus-inf          IEEE floating point rounding mode\n"
    " --round-to-minus-inf         IEEE floating point rounding mode\n"
    " --round-to-zero              IEEE floating point rounding mode\n"
    " --function name              set main function name\n"
    "\n"
    "Program instrumentation options:\n"
    GOTO_CHECK_HELP
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    "\n"
    "Symex options:\n"
    " --unwind nr                  unwind nr times\n"
    " --depth nr                   limit search depth\n"
    " --context-bound nr           limit number of context switches\n"
    " --branch-bound nr            limit number of branches taken\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
