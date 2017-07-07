class interproc1
{
  static void my_method()
  {
    Object o=null;

    my_f(o); // T1 source
    my_g(o);
  }

  static void my_g(Object p)
  {
    my_h(p); // T1 sink
  }

  static void my_f(Object p) { }
  static void my_h(Object p) { }
};

