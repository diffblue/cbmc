#include <assert.h>
#include <stdint.h>
#include <string.h>

#define PACKETBUF_SIZE 128

// Test case for GitHub issue #8593
// When a pointer is initialized outside a function with a cast expression
// pointing to another static storage duration object, CBMC should properly
// handle the dependency and not mark the pointer as invalid.

static uint32_t packetbuf_aligned[(PACKETBUF_SIZE + 3) / 4];
// This pointer initialization depends on packetbuf_aligned being initialized first
uint8_t *packetbuf = (uint8_t *)packetbuf_aligned;

int main()
{
  uint16_t channelId = 0x1234;
  uint8_t *data = packetbuf;

  // This should not fail - data should point to valid memory
  assert(data != 0);

  // Write some data
  memcpy(data, &channelId, 2);

  // Verify the data was written correctly
  uint16_t result;
  memcpy(&result, data, 2);
  assert(result == channelId);

  return 0;
}
