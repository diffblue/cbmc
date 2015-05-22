class assert5
{
  public static void main(String[] args)
  {
    java.util.Random random = new java.util.Random(42);
    
    int i=random.nextInt();
    
    if(i>1000)
      assert i>1000 : "i is greater 1000"; // should hold
  }
}

