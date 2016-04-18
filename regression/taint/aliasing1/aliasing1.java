class aliasing1
{
  static void my_method()
  {
    Object my_o1=my_source();
    
    Object my_o2=new Object();
    my_sink(my_o2); // no flow, as my_o1 and my_o2 are not aliases

    my_sink(my_o1); // flow
  }

  static Object my_source() { return new Object(); }
  static void my_sink(Object p) { }
};

