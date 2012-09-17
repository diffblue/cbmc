#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

// C11: _Alignof
// 6.5.3.4
// The _Alignof operator yields the alignment requirement of its operand
// type.  The operand is not evaluated and the result is an integer
// constant.  When applied to an array type, the result is the alignment
// requirement of the element type.

// The _Alignof operator yields the alignment requirement of its operand
// type.  The operand is not evaluated and the result is an integer
// constant.  When applied to an array type, the result is the alignment
// requirement of the element type.

int f();

STATIC_ASSERT(_Alignof(char)==1);
STATIC_ASSERT(_Alignof(char[10])==1);
STATIC_ASSERT(_Alignof(char[f()])==1);

int main()
{
}
