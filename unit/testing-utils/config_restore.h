/*******************************************************************\

Module: RAII guard for the global configuration object

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_CONFIG_RESTORE_H
#define CPROVER_TESTING_UTILS_CONFIG_RESTORE_H

#include <util/config.h>

/// Restores the global configuration object on destruction, so that the
/// original configuration is re-established even when an assertion fails.
struct config_restoret
{
  configt config_backup = config;

  ~config_restoret()
  {
    config = config_backup;
  }
};

#endif // CPROVER_TESTING_UTILS_CONFIG_RESTORE_H
