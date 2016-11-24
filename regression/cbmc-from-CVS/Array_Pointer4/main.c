// array of pointers
char *a1[10];

// pointer to array
char (*a2)[10];

// array of pointers
char *(a3[10]);

int main()
{
  assert(sizeof(int *)==4 || sizeof(int *)==8);
  assert(sizeof(a1)==10*sizeof(int *));
  assert(sizeof(a2)==sizeof(int *));
  assert(sizeof(a3)==10*sizeof(int *));
}
