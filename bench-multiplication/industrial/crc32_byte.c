#include <stdint.h>
uint32_t crc32_byte(uint32_t crc, uint8_t byte) {
  crc ^= byte;
  for(int i = 0; i < 8; i++) {
    if(crc & 1) crc = (crc >> 1) ^ 0xEDB88320;
    else crc >>= 1;
  }
  return crc;
}
int main() {
  uint32_t crc;
  uint8_t b;
  __CPROVER_assert(crc32_byte(crc, b) == crc32_byte(crc, b), "deterministic");
}
