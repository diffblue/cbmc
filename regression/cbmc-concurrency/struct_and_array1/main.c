#include <pthread.h>

typedef struct st_t
{
  unsigned char x;
  unsigned char y;
} ST;

ST st;

char my_array[10];

_Bool done1, done2;

void *foo1(void *arg1)
{
  st.x = 1;
  my_array[1]=1;
  done1 = 1;
}

void *foo2(void *arg2)
{
  st.y = 1;
  my_array[2]=1;
  done2 = 1;
}

int main()
{
  pthread_t t;
  pthread_create(&t,NULL,foo1,NULL);
  pthread_create(&t,NULL,foo2,NULL);

  if(done1 && done2)
  {
    assert(st.x==st.y);
    assert(my_array[1]==my_array[2]);
  }
}
