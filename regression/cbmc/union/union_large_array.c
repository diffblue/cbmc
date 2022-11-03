#define LARGE 100000

// This is to test the efficiency of unions that contain a large array.
union U
{
  char large_array[LARGE];
  int something_else;
};

int main()
{
  union U u;
  u.something_else = 1234;
  __CPROVER_assert(0, "should fail");
}
