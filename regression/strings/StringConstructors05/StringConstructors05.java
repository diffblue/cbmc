public class StringConstructors05
{
   public static void main(String[] args)
   {
      char[] charArray = {'d', 'i', 'f', 'f', 'b', 'l', 'u', 'e'};
      String s3 = new String(charArray);
      assert s3.equals("diffkblue");
   } 
}

