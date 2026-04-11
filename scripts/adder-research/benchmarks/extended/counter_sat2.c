#include <stdint.h>
#define N 800
int main() {
  uint32_t counter = 0;
  uint8_t flags[N];
  for(int i = 0; i < N; i++)
    if(flags[i]) counter++;
  __CPROVER_assert(counter != 42, "");
}
