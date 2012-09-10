#include <assert.h>

// this is a gcc extension to allow various interfaces

#ifdef __GNUC__

typedef unsigned int pid_t;

union wait {
  int whatnot;
};

typedef union
  {
    int *__ip;
    union wait *__up;
  } wait_status_ptr_t __attribute__ ((__transparent_union__));

pid_t wait(wait_status_ptr_t);

int w1 () { int w; return wait(&w); }
int w2 () { union wait w; return wait(&w); }

pid_t wait(wait_status_ptr_t p)
{
  assert(p.__ip!=0);
}

// alternative syntax

union U
{
  int *p;
  char *q;
} __attribute__((transparent_union));

void f(union U u)
{
}

int main()
{
  int *p;
  char *q;
  f(p);
  f(q);
}

#else

int main()
{
}

#endif
