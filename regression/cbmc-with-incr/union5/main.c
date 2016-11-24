union u_type
{
  int i;
  char ch;
};

int main()
{
  // rest of my_U should be non-deterministic
  union u_type my_U = { .ch = 1 }; 

  // should fail
  assert(my_U.i==1);
}
