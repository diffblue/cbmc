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

// Visual Studio has __alignof

#ifdef _WIN32
#define _Alignof __alignof
#endif

#define _Alignof __alignof__

int f();
int some_var;

STATIC_ASSERT(_Alignof(char)==1);
STATIC_ASSERT(_Alignof(char[10])==1);

// also works without parentheses if it's an expression
STATIC_ASSERT(_Alignof some_var);
STATIC_ASSERT(_Alignof f);

#ifndef _WIN32
// newer versions of gcc and clang eat this
//STATIC_ASSERT(_Alignof(char[f()])==1);
#endif

#ifndef _WIN32
// gcc-specific
struct foo {
  int x;
} __attribute__((aligned(128+0)));

STATIC_ASSERT(_Alignof(struct foo)==128);

// gcc takes the following, but clang doesn't
STATIC_ASSERT(_Alignof(int __attribute__((aligned(128))))==128);
#endif    

int main()
{
}
