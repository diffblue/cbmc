/*******************************************************************\

Module: mmcc Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#if 0
#include <fstream>
#include <cstdlib> // exit()
#include <memory>

#include <util/string2int.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/language.h>
#include <util/unicode.h>
#include <util/memory_info.h>
#include <util/i2string.h>

#include <ansi-c/c_preprocess.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/goto_check.h>

#include <langapi/mode.h>

#include "bmc.h"
#include "xml_interface.h"
#endif

#include <cbmc/version.h>

#include "mmcc_parse_options.h"

/*******************************************************************\

Function: mmcc_parse_optionst::mmcc_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mmcc_parse_optionst::mmcc_parse_optionst(int argc, const char **argv):
  parse_options_baset(MMCC_OPTIONS, argc, argv)
{
}
  
/*******************************************************************\

Function: mmcc_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int mmcc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }
  
  return 0;
}

/*******************************************************************\

Function: mmcc_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void mmcc_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *   MMCC " CBMC_VERSION " - Copyright (C) 2015-2015    * *\n";
    
  std::cout <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " mmcc [-?] [-h] [--help]      show help\n"
    " mmcc file.cat                source file name\n"
    "\n";
}
