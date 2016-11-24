struct A{int i;};
struct B: A {};
struct C: A {};
struct D: virtual B, virtual C {}; // we do not allow this
