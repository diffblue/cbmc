void some_func()
{
}

int main()
{
  void *some_ptr1=
    reinterpret_cast<void *>(&some_func);

  // old style
  void *some_ptr2=
    (void *)(&some_func);

  void (*some_ptr3)(void)=
    reinterpret_cast<void (*)(void)>(some_ptr1);
}
