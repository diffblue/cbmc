#include <stdint.h>
#include <assert.h>

void foo(uint32_t a, uint32_t b) {
    assert(a > b);
}