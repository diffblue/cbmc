public class StringConstructors03
{
   public static void main(String[] args)
   {
      String s = new String("test");
      String s2 = new String(s);
      assert s2.equals("tesst");
   } 
}

