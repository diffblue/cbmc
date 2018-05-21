class basic2
{
  void my_method()
  {
    Object o=null;
    
    my_f(o); // T1 source
    my_h(o); // T1,T2 sink
    
    o=my_g(); // T2 source
    my_h(o); // T1,T2 sink
  }

  void my_f(Object p) { }
  void my_h(Object p) { }
  Object my_g() { return new Object(); }
};

