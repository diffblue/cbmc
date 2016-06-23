class instanceof1
{

  public static void main(String[] args)
  {
    // absolutely everything is an Object
    assert args instanceof Object;
    assert int.class instanceof Object;
    assert "" instanceof String;

    Object o=new Object();
    assert ! (o instanceof String);
  }
  
};
