#include <type.h>

typedef enum { BV_UNKNOWN, BV_NONE, BV_SIGNED, BV_UNSIGNED } bv_semt;

bv_semt bv_sem(const typet &type);

// depreciated, and will disappear
unsigned bv_width(const typet &type);

