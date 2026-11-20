// The element type of an allocation `sizeof(char) * n' is char even when n
// is a constant computed from another sizeof (libstdc++'s
// num_put::_M_insert_int allocates its digit buffer this way).  With a
// buffer of long elements every char store became a byte_update that
// constant propagation could not see through.
int main()
{
  const int ilen = 5 * sizeof(long);
  char *p = __builtin_alloca(sizeof(char) * ilen);
  p[ilen - 2] = '4';
  if(p[ilen - 2] == '4')
    p[ilen - 1] = '2';
  __CPROVER_assert(p[ilen - 1] == '2', "stored");
  return 0;
}
