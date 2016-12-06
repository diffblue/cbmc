int foo;

#ifdef __GNUC__
int* other(int *) __asm__("" "my_real_name");

int *other(int *p) { return p; }
#endif
