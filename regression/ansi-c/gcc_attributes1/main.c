#ifdef __GNUC__

typedef int i32;

i32 __attribute__((aligned)) counter; 

__attribute__((aligned)) __attribute__((aligned)) int x0;
const __attribute__((aligned)) int x1;
static __attribute__((aligned)) int x2;
static const __attribute__((aligned)) int x3;
const __attribute__((aligned)) static int x4;
static __attribute__((aligned)) volatile int x5;
volatile __attribute__((aligned)) const int x6;
int x7 __attribute__((aligned));
int x8 __attribute__((aligned)) = 1;
int x9 __attribute__((aligned)),
   x10 __attribute__((aligned)) = 1;
int (*x)() __attribute__((aligned));
int __attribute__((aligned)) x11;
char *__attribute__((aligned(8))) *fptrasd1;
char *__attribute__((aligned(8))) fptrasd2;
char __attribute__((aligned(8))) *fptrasd3;

int (__attribute__((aligned)) xx);
int (__attribute__((aligned)) (xx));
void (__attribute__((aligned)) *****f1)(void);
void (__attribute__((aligned)) f3)(void);

enum __attribute__((aligned)) { asd1 };
enum { asd2 } __attribute__((aligned));
enum __attribute__((aligned)) my_enum { asd3 };

void test(int (__attribute__((aligned)) x))
{
}

//
// noreturn
//

__attribute__((noreturn))
void my_f1()
{
  while(1);
}

//
// unused
//

int my_f2()
{
label: __attribute__((unused));
}

//
// packed
//

__attribute__((aligned)) struct tag {
  int f;
} __attribute__((packed)) my_struct;

__attribute__((aligned)) struct tag2 {
  int f;
} __attribute__((packed));

struct my_struct_whatnot
{
  __attribute((packed)) int w:2;
  int __attribute__((packed)) x:2, y:2;
  int z:2 __attribute__((packed));
};

struct __attribute__((packed)) tag3
{
  int f;
};

//
// aligned
//
// the aligned attribute has an _optional_ argument
//

struct a_tag1 { short f[3]; } __attribute__ ((aligned (8)));
struct a_tag2 { short f[3]; } __attribute__ ((aligned));

char *const __attribute__((aligned(8))) *f2;

typedef struct { } some_typedef __attribute__ ((__aligned__));

// all sorts of places!
__attribute__((__aligned__)) int gvar1;
int __attribute__((__aligned__)) gvar2;
int gvar3 __attribute__((__aligned__));

// together with s.th. else
struct Scomb {
  int x;
} __attribute__ ((packed, aligned (64)));
                
#endif

int main()
{
}
