#include <stdint.h>
uint16_t checksum(uint16_t *data, int len) {
  uint32_t sum = 0;
  for(int i = 0; i < len; i++)
    sum += data[i];
  while(sum >> 16)
    sum = (sum & 0xFFFF) + (sum >> 16);
  return ~sum;
}
int main() {
  uint16_t data[4];
  uint16_t c1 = checksum(data, 4);
  uint16_t c2 = checksum(data, 4);
  __CPROVER_assert(c1 == c2, "deterministic");
}
