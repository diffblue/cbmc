/*******************************************************************\

Module: Language Features

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Features

#ifndef CPROVER_GOTO_PROGRAMS_LANGUAGE_FEATURES_H
#define CPROVER_GOTO_PROGRAMS_LANGUAGE_FEATURES_H

#include <util/irep.h>

class abstract_goto_modelt;
class goto_modelt;
class symbol_tablet;

/// Returns true when the given goto model indicates that
/// the given language feature might be used.
bool has_language_feature(const abstract_goto_modelt &, const irep_idt &);
bool has_language_feature(const symbol_tablet &, const irep_idt &);

/// Indicate that the given goto model might use
/// the given language feature.
void add_language_feature(goto_modelt &, const irep_idt &);
void add_language_feature(symbol_tablet &, const irep_idt &);

/// Indicate that the given goto model does not use
/// the given language feature.
void clear_language_feature(goto_modelt &, const irep_idt &);
void clear_language_feature(symbol_tablet &, const irep_idt &);

#endif // CPROVER_GOTO_PROGRAMS_LANGUAGE_FEATURES_H
