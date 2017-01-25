/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <iostream>

#include <cegis/cegis-util/temporary_output_block.h>

temporary_output_blockt::temporary_output_blockt()
{
  std::cout.setstate(std::ios_base::failbit);
}

temporary_output_blockt::~temporary_output_blockt()
{
  release();
}

void temporary_output_blockt::release() const
{
  std::cout.clear();
}
