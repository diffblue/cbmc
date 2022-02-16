/*******************************************************************\

Module: Read Goto Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Read Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_LINK_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_LINK_GOTO_MODEL_H

#include <util/nodiscard.h>
#include <util/replace_symbol.h>

class goto_modelt;
class message_handlert;

/// Link goto model \p src into goto model \p dest, invalidating \p src in this
/// process. Linking may require updates to object types contained in \p dest,
/// which need to be applied using \ref finalize_linking.
/// \return nullopt if linking fails, else a (possibly empty) collection of
///   replacements to be applied.
NODISCARD optionalt<replace_symbolt::expr_mapt>
link_goto_model(goto_modelt &dest, goto_modelt &&src, message_handlert &);

/// Apply \p type_updates to \p dest, where \p type_updates were constructed
/// from one or more calls to \p link_goto_model.
void finalize_linking(
  goto_modelt &dest,
  const replace_symbolt::expr_mapt &type_updates);

#endif // CPROVER_GOTO_PROGRAMS_LINK_GOTO_MODEL_H
