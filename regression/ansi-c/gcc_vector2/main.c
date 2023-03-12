typedef int __v4 __attribute__((__vector_size__(16)));
typedef int __v8 __attribute__((__vector_size__(32)));
typedef int __v16 __attribute__((__vector_size__(64)));

__v8 foo(__v16 __A)
{
  union
  {
    __v8 __a[2];
    __v16 __v;
  } __u = {.__v = __A};
  return __u.__a[0];
}

__v4 bar(__v8 __A)
{
  union
  {
    __v4 __a[2];
    __v8 __v;
  } __u = {.__v = __A};
  return __u.__a[0];
}

int main()
{
}
