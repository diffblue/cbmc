int x = 123;
int y;

// should also work through a typedef
typedef unsigned char uchar;
uchar b[] = "abc";

// addresses are constants
int *p=&y;

// we need to allow incomplete structs for #include <stdio.h>
extern struct _IO_FILE_plus _IO_2_1_stdin_;

int some_func()
{
  static int some_static; // zero initialized
  return some_static;
}

int main()
{
  assert(x == 123);
  assert(y == 0);
  assert(b[0]=='a');
  assert(some_func()==0);  
  assert(p==&y);
}
