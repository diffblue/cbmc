class basic2
{
  void my_method()
  {
    Object o=null;
    
    my_f(o); // source
    my_h(o); // sink
    
    o=my_g(); // source
    my_h(o); // sink
  }

  void my_f(Object p) { }
  void my_h(Object p) { }
  Object my_g() { return new Object(); }
};

