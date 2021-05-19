typedef struct test {
  int id;
} test;

int main(int argc, char **argv) {

  const float *pc = (const float []){1e0, 1e1, 1e2};

start:;
  test newAlloc0 = {0};
  if(argv[0])
  {
    test newAlloc1 = {1};
    goto start;
  }

  if(argv[1])
  {
    test newAlloc2 = {2};
    if (argv[2])
    {
      test newAlloc3 = {3};
    nested_if:;
      test newAlloc5 = {5};
      if (argv[3])
      {
        return 1;
      }
      else
      {
        goto end;
      }
    }
    else
    {
      test newAlloc4 = {4};
      test newAlloc6 = {6};
      test newAlloc7 = {7};
      goto nested_if;
    }
  }

end:
  return 0;
}
