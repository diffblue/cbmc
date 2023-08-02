#include <assert.h>
#include <stdint.h>
#include <stdio.h>

#define ARRAYMAX 256

uint8_t *strndfy (uint8_t *dest, const uint8_t *src, size_t n) {
  int i = 0;
  int j = 0;
  
  switch (n & 0x3) {
    do {
      case 0 :   dest[i++] = src[j++];
      case 1 :   dest[i++] = src[j++];
      case 2 :   dest[i++] = src[j++];
      case 3 :   dest[i++] = src[j++];
    } while (j < n);
  }
  
  return dest;
}


int main (int argc, char **argv) {
  uint8_t src[ARRAYMAX];
  uint8_t dest[ARRAYMAX];
  
  int length = 0;  
  scanf("%u", &length);

  if (length <= ARRAYMAX) {
    for (int i = 0; i < length; ++i) {
      src[i] = (uint8_t)i;
    }

    strndfy(dest, src, length);
    
    for (int i = 0; i < length; ++i) {
      assert(dest[i] == (uint8_t)i);
    }
  }
  
  return 0;
}
