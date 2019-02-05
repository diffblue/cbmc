/*******************************************************************\

Module: Output of the verification conditions (VCCs)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Output of the verification conditions (VCCs)

#ifndef CPROVER_GOTO_SYMEX_SHOW_VCC_H
#define CPROVER_GOTO_SYMEX_SHOW_VCC_H

#include <util/ui_message.h>

class optionst;
class symex_target_equationt;

/// Output equations from \p equation to a file or to the standard output.
/// The name of the output file is given by the `outfile` option from
/// \p options, the standard input is used if it is not provided.
/// The format is either JSON or plain text depending on \p ui_message_handler;
/// XML is not supported.
/// See \link show_vcc_json \endlink and \link show_vcc_plain \endlink
void show_vcc(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  const symex_target_equationt &equation);

#endif // CPROVER_GOTO_SYMEX_SHOW_VCC_H
