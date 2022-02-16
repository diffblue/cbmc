#include <stdint.h>
#include <stdlib.h>

// HAVOC STRUCT MEMBERS
// TODO take into account plaform/pointer size in the tests
typedef struct
{
  uint16_t a;    // 2 bytes
  uint16_t b[5]; // 10 bytes
  uint32_t c;    // 4 bytes
  uint16_t *d;   // 4 or 8 bytes
  union {
    uint16_t a;    // 2 bytes
    uint16_t b[5]; // 10 bytes
    uint32_t c;    // 4 bytes
    uint16_t *d;   // 4 or 8 bytes
  } u;             // 10 bytes
} st;              // 30 or 34 bytes total

//                0  2          12   16       24       34
//                |  |          |    |        |        |
// struct layout: aa bbbbbbbbbb cccc dddddddd uuuuuuuuuu
// union layout :                             aa--------
//                                            bbbbbbbbbb
//                                            cccc------
//                                            dddddddd--
