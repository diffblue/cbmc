/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FORMAT_SPEC_H
#define CPROVER_FORMAT_SPEC_H

class format_spect
{
public:
  format_spect():min_width(0), precision(6), zero_padding(false)
  {
  }

  unsigned min_width;
  unsigned precision;
  bool zero_padding;
};

#endif
