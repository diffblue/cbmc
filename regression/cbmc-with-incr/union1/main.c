union u_type
{
  int i;
  char ch;
};

// rest of my_U should be zero
union u_type my_U = { .ch = 1 };

int main()
{
  // little and big endian case, assuming sizeof(int)==4
  assert(my_U.i==1 || my_U.i==0x01000000);

  union u_type u;

  u.i=1;
  assert(u.i==1);

  u.ch=2;
  assert(u.ch==2);
}
