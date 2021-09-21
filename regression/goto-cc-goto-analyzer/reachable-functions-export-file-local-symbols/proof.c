int __CPROVER_file_local_project_c_foo(int x);

int main()
{
  int x = __CPROVER_file_local_project_c_foo(1);
  assert(x == 2);
}
