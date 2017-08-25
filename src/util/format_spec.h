/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FORMAT_SPEC_H
#define CPROVER_UTIL_FORMAT_SPEC_H

// this mimics the 'printf' format string for a single 'directive'

class format_spect
{
public:
  unsigned min_width;
  unsigned precision;
  bool zero_padding;

  // 'printf' equivalents:
  // fF: DECIMAL
  // eE: SCIENTIFIC
  // gG: AUTOMATIC

  enum class stylet { DECIMAL, SCIENTIFIC, AUTOMATIC };
  stylet style;

  format_spect():
    min_width(0),
    precision(6),
    zero_padding(false),
    style(stylet::AUTOMATIC)
  {
  }

  explicit format_spect(stylet _style):
    min_width(0),
    precision(6),
    zero_padding(false),
    style(_style)
  {
  }

  static format_spect scientific()
  {
    return format_spect(stylet::SCIENTIFIC);
  }

  static format_spect automatic()
  {
    return format_spect(stylet::AUTOMATIC);
  }
};

#endif // CPROVER_UTIL_FORMAT_SPEC_H
