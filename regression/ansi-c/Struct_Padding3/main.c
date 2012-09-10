#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

#ifndef __GNUC__
#define __builtin_offsetof(a, b) ((unsigned long long)&(((a *)0)->b))
#endif

struct my_struct1a {
  char ch1;
  int i; // this would normally be padded, but it won't!
  char ch2;
} __attribute__((packed));

struct my_struct1b {
  char ch1;
  // this would normally be padded, but it won't!
  int i __attribute__((packed)); 
  char ch2;
};

struct my_struct1c {
  char ch1;
  // this would normally be padded, but it won't!
  struct
  {
    int i; 
  } sub __attribute__((packed));
  char ch2;
};

struct my_struct1d {
  char ch0;
  // the next field isn't padded
  struct
  {
    char ch1;
    int i; // this _is_ padded!
  } sub __attribute__((packed));
  char ch2;
};

struct __attribute__((packed)) my_struct2 {
  char ch1;
  int i; // this would normally be padded, but it won't!
  char ch2;
};

struct my_struct3 {
  char ch1;
  char ch2;
  int i1; // this should be padded for 4-byte alignment
  char ch3;
  long long i2; // this should be padded for 8-byte alignment
};

STATIC_ASSERT(__builtin_offsetof(struct my_struct1a, i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1a, ch2)==5);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1b, i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1b, ch2)==5);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1c, sub.i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1c, ch2)==5);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1d, sub.ch1)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1d, sub.i)==5);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1d, ch2)==9);

STATIC_ASSERT(__builtin_offsetof(struct my_struct2, i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct2, ch2)==5);

STATIC_ASSERT(__builtin_offsetof(struct my_struct3, ch1)==0);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, ch2)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, i1)==4);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, ch3)==8);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, i2)==16);

int main()
{
}

