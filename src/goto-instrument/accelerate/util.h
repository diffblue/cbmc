#ifndef ACCELERATE_UTIL_H
#define ACCELERATE_UTIL_H

#include <util/std_types.h>
#include <util/config.h>

#define POLY_WIDTH config.ansi_c.long_int_width

typet join_types(const typet &t1, const typet &t2);

#endif // ACCELERATE_UTIL_H
