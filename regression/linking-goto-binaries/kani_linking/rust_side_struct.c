#include <stdint.h>
#include <assert.h>
#include <stdlib.h>

struct Unit {};
struct PhantomData {};

// Change to make it not compatable
struct ABCDE {
    uint8_t c;
    struct Unit u;
    float d;
    int64_t i;
};

struct ABCDE generates_mixed_field_struct(uint8_t c, uint32_t d, int64_t i);

void test_mixed_field_struct() {
    uint8_t c;
    uint32_t d;
    int64_t i;
    struct ABCDE result =  generates_mixed_field_struct(c,d,i);
    assert(c == result.c);
    assert(d == result.d);
    assert(i == result.i);
}

void main() {
    test_mixed_field_struct();
}
