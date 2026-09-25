// cvise reduction (valgrind-clean, UBSan-clean) of cpp20_map_basic's
// false positive "m[1] == 42: FAILURE" to 3 cooperating shapes from
// libstdc++'s map machinery:
//  1. membuft = __aligned_membuf: `alignas(int) char` storage.  CBMC
//     lays it out with sizeof 1 instead of 4 (see
//     cpp11_alignas_member_layout), so the store through the pairt
//     lens is out of bounds and the load yields garbage.
//  2. comparet : emptyt = _Rb_tree's less/binary_function pair; the
//     synthesized copy assignment of the empty-base-only class emits a
//     struct-to-base typecast that reaches the SAT encoder and is
//     dropped ("warning: ignoring typecast") -- only in combination
//     with shape 3's punned dereference.
//  3. the iterator's operator* returning a reference through a
//     static_cast<pairt *>(void-pointer-to-membuf), libstdc++'s
//     _M_valptr() pattern.
//
// N5008 [dcl.align], [expr.sizeof]/2 (layout); [class.copy.assign]/12
// (base subobject assignment).  g++/clang++ accept, static_assert
// sizeof(membuft)==sizeof(int), and verify at runtime.
//
// FIXED by the alignas layout fix: with the correct membuft size the
// store is in bounds; the empty-base assignment then folds away before
// the encoder (no dropped constraint remains).
extern "C" void __CPROVER_assert(bool, const char *);

struct pairt
{
  int second;
};

struct emptyt
{
};

struct comparet : emptyt
{
};

struct membuft
{
  alignas(int) char storage;
};

comparet global_compare;
membuft global_buf;
void *buf_ptr;

struct iteratort
{
  pairt &operator*()
  {
    buf_ptr = &global_buf;
    return *static_cast<pairt *>(buf_ptr);
  }
};

struct mapt
{
  int &operator[](int)
  {
    comparet cmp;
    iteratort it;
    cmp = global_compare;
    return (*it).second;
  }
};

int main()
{
  mapt m;
  m[1] = 42;
  __CPROVER_assert(m[1] == 42, "stored value survives");
  return 0;
}
