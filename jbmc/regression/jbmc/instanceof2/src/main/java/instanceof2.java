class instanceof2
{
  public static void main(String[] args)
  {
    // Check that the java.lang.Class instance representing a primitive type,
    // here 'int', passes a trivial instanceof check.
    // Note these compile to references to static fields of boxing types, here
    // java.lang.Integer.TYPE.
    assert int.class instanceof Object;
  }
};
