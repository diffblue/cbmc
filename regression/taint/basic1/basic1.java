class basic1
{
  static void my_method()
  {
    Object o=null;
    
    my_f(o); // source
    my_h(o); // sink
    
    o=my_g(); // source
    my_h(o); // sink
  }

  static void my_f(Object p) { }
  static void my_h(Object p) { }
  static Object my_g() { return new Object(); }
};

