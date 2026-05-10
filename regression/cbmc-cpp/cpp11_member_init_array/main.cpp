// Per [dcl.init]/8: value-initialization of an array member via T()
// in a constructor's member-initializer list zero-initializes each
// element.  Before the fix in cpp_typecheck_code.cpp, CBMC emitted a
// direct assignment to the array lvalue, which [expr.ass] forbids,
// producing "direct assignments to arrays not permitted" at
// type-check time.
//
// This pattern is used by MSVC's <xstring> for the SSO buffer:
//   union _Bxty {
//     value_type _Buf[_BUF_SIZE];
//     pointer _Ptr;
//     inline _Bxty() noexcept : _Buf() {}
//     ...
//   };

struct has_array
{
  int arr[4];
  has_array() : arr()
  {
  }
};

struct has_array_char
{
  char buf[16];
  has_array_char() : buf()
  {
  }
};

int main()
{
  has_array h;
  __CPROVER_assert(h.arr[0] == 0, "int array value-init: [0]");
  __CPROVER_assert(h.arr[1] == 0, "int array value-init: [1]");
  __CPROVER_assert(h.arr[3] == 0, "int array value-init: [3]");

  has_array_char hc;
  __CPROVER_assert(hc.buf[0] == 0, "char array value-init: [0]");
  __CPROVER_assert(hc.buf[15] == 0, "char array value-init: [15]");
  return 0;
}
