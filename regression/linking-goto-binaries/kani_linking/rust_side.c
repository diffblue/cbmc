
#include <stdint.h>
#include <assert.h>
#include <stdlib.h>

struct Unit {};
struct PhantomData {};
struct OptionU32Ptr {
    uint32_t* ptr;
};

struct OptionU32PtrWithPhantomData {
    uint32_t* ptr;
    struct PhantomData pd;
};


struct OptionU32PtrWithPhantomDataFirst {
    struct PhantomData pd;
    uint32_t* ptr;
};

struct Unit foo(uint32_t a, uint32_t b);
struct Unit bar(struct OptionU32Ptr p);

struct OptionU32PtrWithPhantomDataFirst returns_ptr(uint32_t a, uint32_t b);


void test_foo() {
    uint32_t a;
    uint32_t b;
    __CPROVER_assume(a > b);
    struct Unit tmp = foo(a,b);
}

void test_ptr() {
    uint32_t a;
    uint32_t b;
    // No overflow
    __CPROVER_assume(a < 1000);
    __CPROVER_assume(b < 1000);
    struct OptionU32PtrWithPhantomDataFirst p = returns_ptr(a,b);
    assert(*p.ptr == a+b); // Should pass
    assert(*p.ptr == a); // Should fail
}

struct MultiFieldStruct {
    uint8_t c;
    uint32_t d;
    int64_t i;
};

// Use a mix of types, and has padding
struct MultiFieldStructA {
    uint8_t c;
    struct Unit u;
    uint32_t d;
    int64_t i;
};

// Change to make it not compatable
struct MultiFieldStructB {
    uint8_t c;
    struct Unit u;
    float d;
    int64_t i;
    char x;
};

struct MultiFieldStructB generates_mixed_field_struct(uint8_t c, uint32_t d, int64_t i);

void test_mixed_field_struct() {
    uint8_t c;
    uint32_t d;
    int64_t i;
    struct MultiFieldStructB result =  generates_mixed_field_struct(c,d,i);
    assert(c == result.c);
    assert(d == result.d);
    assert(i == result.i);
}



void main() {
    test_mixed_field_struct();
}
