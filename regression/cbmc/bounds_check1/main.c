#include <stdint.h>
#include <stdlib.h>

typedef struct _eth_frame_header
{
  uint8_t dest[6];
  uint8_t src[6];
  uint16_t length;
  uint8_t payload[0];
} eth_frame_header;

typedef struct _eth_frame_header_with_tag
{
  uint8_t dest[6];
  uint8_t src[6];
  uint32_t tag;
  uint16_t length;
  uint8_t payload[0];
} eth_frame_header_with_tag;

typedef struct _eth_frame_footer
{
  uint32_t crc;
} eth_frame_footer;

#define FRAME_LENGTH                                                           \
  sizeof(eth_frame_header_with_tag) + 1500 + sizeof(eth_frame_footer)

typedef union _eth_frame {
  uint8_t raw[FRAME_LENGTH];
  eth_frame_header header;
  eth_frame_header_with_tag header_with_tag;
} eth_frame;

typedef struct _eth_frame_with_control
{
  eth_frame frame;
  uint32_t control; // Routing, filtering, inspection, etc.
} eth_frame_with_control;

void stack()
{
  eth_frame_with_control f;
  unsigned i, i2, j, j2, k, k2, l, l2;

  // Safe if 0 <= i < FRAME_LENGTH, viable attack over FRAME_LENGTH
  __CPROVER_assume(i < FRAME_LENGTH);
  // within array bounds
  f.frame.raw[i] = 42;
  __CPROVER_assume(i2 < FRAME_LENGTH + 4);
  // possibly out-of-bounds, even though still within the object
  f.frame.raw[i2] = 42;

  // Safe if 0 <= j < 6, likely unsafe if over 6
  __CPROVER_assume(j < 6);
  // within array bounds
  f.frame.header.dest[j] = 42;
  // possibly out-of-bounds
  f.frame.header.dest[j2] = 42;

  // Safe if 0 <= k < 1500, could corrupt crc if k < 1508, viable attack over 1508
  __CPROVER_assume(k < FRAME_LENGTH - 14);
  // within array bounds
  f.frame.header.payload[k] = 42;
  // possibly out-of-bounds
  f.frame.header.payload[k2] = 42;

  // Safe if 0 <= l < 1504, wrong but probably harmless if l < 1508, viable attack over 1508
  __CPROVER_assume(l < FRAME_LENGTH - 14);
  // within array bounds
  ((eth_frame_footer *)(&(f.frame.header.payload[l])))->crc = 42;
  // possibly out-of-bounds
  ((eth_frame_footer *)(&(f.frame.header.payload[l2])))->crc = 42;
}

void heap()
{
  eth_frame_with_control *f_heap = malloc(sizeof(eth_frame_with_control));
  unsigned i, i2, j, j2, k, k2, l, l2;

  // Safe if 0 <= i < FRAME_LENGTH, viable attack over FRAME_LENGTH
  __CPROVER_assume(i < FRAME_LENGTH);
  // within array bounds
  f_heap->frame.raw[i] = 42;
  __CPROVER_assume(i2 < FRAME_LENGTH + 4);
  // possibly out-of-bounds, even though still within the object
  f_heap->frame.raw[i2] = 42;

  // Safe if 0 <= j < 6, likely unsafe if over 6
  __CPROVER_assume(j < 6);
  // within array bounds
  f_heap->frame.header.dest[j] = 42;
  // possibly out-of-bounds
  f_heap->frame.header.dest[j2] = 42;

  // Safe if 0 <= k < 1500, could corrupt crc if k < 1508, viable attack over 1508
  __CPROVER_assume(k < FRAME_LENGTH - 14);
  // within array bounds
  f_heap->frame.header.payload[k] = 42;
  // possibly out-of-bounds
  f_heap->frame.header.payload[k2] = 42;

  // Safe if 0 <= l < 1504, wrong but probably harmless if l < 1508, viable attack over 1508
  __CPROVER_assume(l < FRAME_LENGTH - 14);
  // within array bounds
  ((eth_frame_footer *)(&(f_heap->frame.header.payload[l])))->crc = 42;
  // possibly out-of-bounds
  ((eth_frame_footer *)(&(f_heap->frame.header.payload[l2])))->crc = 42;
}

int main()
{
  stack();
  heap();
}
