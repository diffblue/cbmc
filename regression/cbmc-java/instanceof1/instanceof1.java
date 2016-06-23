class instanceof1
{
  public static void main(String[] args)
  {
    // absolutely everything is an Object
    assert args instanceof Object;
    assert int.class instanceof Object;
    
    // args is an array
    assert args instanceof Object[];
    
    // string literals are strings
    assert "" instanceof String;

    // need a negative example, too
    Object o=new Object();
    assert ! (o instanceof String);
  }
};
