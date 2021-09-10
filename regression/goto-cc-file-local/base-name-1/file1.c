int __CPROVER_file_local_file2_c_foo(int x);

int main()
{
  int x = __CPROVER_file_local_file2_c_foo(1);
  __CPROVER_assert(x == 2, "x == 2");
}
