#include <assert.h>

#ifdef __GNUC__
typedef int base_type;

typedef base_type v4si __attribute__((vector_size(16)));

typedef union
{
  v4si v;
  base_type members[4];
} vector_u;

int main()
{
  assert(sizeof(int)==4);
  assert(sizeof(v4si)==16);

  vector_u x, y, z;
  
  z.v=x.v+y.v;

  assert(z.members[0]==x.members[0]+y.members[0]);
  assert(z.members[1]==x.members[1]+y.members[1]);
  assert(z.members[2]==x.members[2]+y.members[2]);
  assert(z.members[3]==x.members[3]+y.members[3]);

  z.v=x.v-y.v;

  assert(z.members[0]==x.members[0]-y.members[0]);
  assert(z.members[1]==x.members[1]-y.members[1]);
  assert(z.members[2]==x.members[2]-y.members[2]);
  assert(z.members[3]==x.members[3]-y.members[3]);

  z.v=-x.v;

  assert(z.members[0]==-x.members[0]);
  assert(z.members[1]==-x.members[1]);
  assert(z.members[2]==-x.members[2]);
  assert(z.members[3]==-x.members[3]);

  z.v=~x.v;

  assert(z.members[0]==~x.members[0]);
  assert(z.members[1]==~x.members[1]);
  assert(z.members[2]==~x.members[2]);
  assert(z.members[3]==~x.members[3]);
  
  // build vector with typecast
  z.v=(v4si){ 0, 1, 2, 3 };
  assert(z.members[0]==0 && z.members[1]==1 && z.members[2]==2 && z.members[3]==3);

  // build vector with initializer
  v4si some_vector={ 10, 11, 12, 13 };
  z.v=some_vector;
  assert(z.members[0]==10 && z.members[1]==11 && z.members[2]==12 && z.members[3]==13);
  
  // same from one
  v4si other_vector={ 0 };
  z.v=other_vector;
  
  assert(z.members[1]==0);
}

#else

int main()
{
}

#endif
