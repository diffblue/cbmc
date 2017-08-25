#include <stdlib.h>
#include <stdint.h>

typedef union {
  struct {
    uint8_t x;
    uint8_t z;
  } b;
} union_t;

typedef struct {
    uint32_t magic;
    union_t unions[];
} flex;

int flex_init(flex * flex, size_t num)
{
    if (num == 0 || num >= 200) {
        return -1;
    }
    flex->unions[num - 1].b.z = 255;
    return 0;
}

int main() {
    uint8_t num = nondet_size();
    flex * pool = (flex *) malloc(sizeof(flex) + num * sizeof(union_t));
    int ret = flex_init(pool, num);
    if (num > 0 && num < 200) {
        __CPROVER_assert(ret == 0, "Accept inside range");
    } else {
        __CPROVER_assert(ret != 0, "Reject outside range");
    }
}

