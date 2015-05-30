/*******************************************************************
 Module:

 Author: Daniel Kroening, kroening@kroening.com

 \*******************************************************************/

#ifndef CPROVER_JAVA_ENTRY_POINT_H
#define CPROVER_JAVA_ENTRY_POINT_H

#include <util/irep.h>

bool java_entry_point(
  class symbol_tablet &symbol_table,
  const irep_idt &main_class,
  class message_handlert &message_handler);

#endif
