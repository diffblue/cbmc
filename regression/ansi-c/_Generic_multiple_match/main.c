int main(void)
{
  // C11 6.5.1.1p2: no two generic associations shall specify compatible types.
  // int(*)[5] is compatible with both int(*)[] and int(*)[5], so this generic
  // selection is a constraint violation. GCC and Clang both reject it; CBMC
  // must too rather than silently picking one association.
  int arr[5];
  return _Generic(&arr, int(*)[] : 1, int(*)[5] : 2);
}
