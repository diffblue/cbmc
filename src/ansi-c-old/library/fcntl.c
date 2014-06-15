/* FUNCTION: fcntl */

#ifndef __CPROVER_FCNTL_H_INCLUDED
#include <fcntl.h>
#define __CPROVER_FCNTL_H_INCLUDED
#endif

int fcntl(int fd, int cmd, ...)
{
__CPROVER_HIDE:;
  int return_value;
  (void)fd;
  (void)cmd;
  return return_value;
}
