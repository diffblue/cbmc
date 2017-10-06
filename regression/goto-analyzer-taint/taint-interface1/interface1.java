interface my_I
{
  public Object my_source();
};

class some_class implements my_I
{
  public Object my_source() { return new Object(); }
};

class interface1
{
  void my_method()
  {
    some_class x1=new some_class();

    Object o=x1.my_source();
    my_sink(o);
  }

  void my_sink(Object p) { }
};

