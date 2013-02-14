#ifdef _MSC_VER

// Visual Studio has __builtin_alignof, but gcc doesn't!
int int_align=__builtin_alignof(int);

int int_align2=__alignof(int);

void f1() { __asm { mov ax, ax } }

void f2() { __assume(1); }

int *pBased;
typedef int __based(pBased) * pBasedPtr;

// __box

void __cdecl f3();

__declspec(thread) int thread_local;

//__delegate int GetDayOfWeek();

// __event 

void f4()
{
  __try { } __except(1) { }
}

void __fastcall f5();

void f6()
{
  __try { } __finally { }
}

void __forceinline f7();

// __gc

// __hook

//void __identifier(void);

__if_exists(asd) { };

__if_not_exists(asd) { };

__inline void f8();

__int16 i16;

__int32 i32;

__int64 i64;

__int8 i8;

// __interface 

void f9()
{
  __try { __leave; } __finally { }
}

//__m128 var_m128;

//__m128d var_m128d;

//__m128i var_m128i;

//__m64 var_m64;

// __multiple_inheritance

// __nogc

// __noop

// __pin

// __property

// __raise 

// __sealed

// __single_inheritance

void __stdcall f10();

// __super

// __thiscall

// __try/__except, __try/__finally

// __try_cast

//int __unaligned *unaligned_int_ptr;

// __unhook

// __uuidof

// __value

// __virtual_inheritance

// __w64

// __wchar_t some_wchar;

// wchar_t some_other_wchar;

#endif

int main()
{
}
