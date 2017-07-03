class map1
{
  static void my_method()
  {
    java.util.Map<Integer, Object> my_map=
      new java.util.HashMap<Integer, Object>();

    Object my_o1=my_source();
    my_map.put(0, my_o1);
    
    Object my_o2=my_map.get(0);
    my_sink(my_o2);
  }

  static Object my_source() { return new Object(); }
  static void my_sink(Object p) { }
};

