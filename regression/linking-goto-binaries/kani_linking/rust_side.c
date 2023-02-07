
#include <stdint.h>

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




int main() {
    uint32_t a;
    uint32_t b;
    __CPROVER_assume(a > b);
    struct Unit tmp = foo(a,b);
}
