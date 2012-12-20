typedef unsigned DWORD;
typedef signed LONG;
typedef long long LONGLONG;

typedef union _LARGE_INTEGER {
    struct {
        DWORD LowPart;
        LONG HighPart;
    };
    struct {
        DWORD LowPart;
        LONG HighPart;
    } u;

    LONGLONG QuadPart;
} LARGE_INTEGER;

int main()
{
  LARGE_INTEGER l;
  
  l.QuadPart=1;
  l.LowPart=2;
  l.u.LowPart=3;
  assert(l.LowPart==3);
}

