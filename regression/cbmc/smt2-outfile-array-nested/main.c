// Wider-coverage companion to ../smt2-outfile-array: exercises the
// non-as-const unflatten path on a multi-dimensional array, where the
// outer array's element type is itself an array. The
// find_symbols_rec recursion must declare an unflatten_base_* for both
// the inner and outer array types, and unflatten must then nest its
// store-chain through both levels without forward-referencing the
// auxiliary names.

struct S
{
  int data[2][2];
  int x;
};

struct S nondet_S(void);

int main()
{
  struct S s = nondet_S();
  int arr[2][2];
  arr[0][0] = s.data[0][0];
  arr[0][1] = s.data[0][1];
  arr[1][0] = s.data[1][0];
  arr[1][1] = s.data[1][1];
  __CPROVER_assert(arr[0][0] == arr[1][1], "check");
  return 0;
}
