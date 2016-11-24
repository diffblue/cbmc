#ifndef __MODULES_H__
#define __MODULES_H__

#include "kdev_t.h"

extern int usecount;

#define MOD_INC_USE_COUNT   (usecount = usecount + 1)
#define MOD_DEC_USE_COUNT   (usecount = usecount - 1)
#define MOD_IN_USE          (usecount != 0)

#define ENODEV              0xf
#define MAJOR_NUMBER        42

extern int register_chrdev (unsigned int, const char *);
extern int unregister_chrdev (unsigned int, const char *);

#endif
