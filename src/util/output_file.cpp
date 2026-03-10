/*******************************************************************\

Module: Output File Container

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Output file container that handles stdout ("-") and regular files

#include "output_file.h"

#include "exception_utils.h"
#include "unicode.h"

#include <fstream>
#include <iostream>

output_filet::output_filet(std::string file_name) : _name(std::move(file_name))
{
  if(_name == "-")
  {
    _stream = &std::cout;
    _name = "stdout";
  }
  else
  {
    _ofstream = std::make_unique<std::ofstream>(widen_if_needed(_name));
    if(!*_ofstream)
      throw system_exceptiont("failed to open " + _name);
    _stream = _ofstream.get();
  }
}

output_filet::~output_filet() = default;
