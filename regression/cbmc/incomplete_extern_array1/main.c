// Indexing into an `extern T arr[]` (an array of unknown size) declared in a
// translation unit of its own. The Linux kernel does this via <linux/ctype.h>'s
// `extern const unsigned char _ctype[]` and the `__ismask(c)` macro, which
// expands to `_ctype[c]`. When the C front end changed the type of such an
// array in the symbol table, but not in the program, the flattening back end
// encoded it inconsistently and failed an invariant.

extern const unsigned char _ctype[];

int nondet_int(void);

int main(void)
{
  int c = nondet_int();
  if(c >= 0 && c < 128)
  {
    unsigned char m1 = _ctype[c];
    unsigned char m2 = _ctype[c + 1];
    // reading the same element again, at a constant or a symbolic index,
    // must yield the same value
    __CPROVER_assert(_ctype[c] == m1, "same index yields the same value");
    if(c == 0)
      __CPROVER_assert(_ctype[0] == m1, "constant index yields the same value");
    return m1 + m2;
  }
  return 0;
}
