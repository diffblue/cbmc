#include <stdint.h>
#include <assert.h>
#include <stdlib.h>

void foo(uint32_t a, uint32_t b) {
    assert(a > b);
}

uint32_t* returns_ptr(uint32_t a, uint32_t b) {
    uint32_t* p = malloc(sizeof(p));
    if (p) *p = a + b;
    return p;
}