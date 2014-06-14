struct gendisk {
  void (*request_fn)(int);
};

struct my_gendisk {
  struct gendisk gd;
};

void test_func(int i)
{
  assert(0);

  return;
}

int main()
{
  struct my_gendisk mydisk;

  mydisk.gd.request_fn = test_func;

  (* mydisk.gd.request_fn)(10);

  return 0;
}
