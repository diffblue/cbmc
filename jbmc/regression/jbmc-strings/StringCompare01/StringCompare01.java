public class StringCompare01
{
   public static void main(String[] args)
   {
      String s1 = new String("test");
      String s2 = "goodbye";
      String s3 = "Automatic Test Generation";
      String s4 = "automatic test generation";

      if (s1.equals("test"))  // true
         assert true;
      else
         assert false;

      if (s1 != "test")  // true; they are not the same object
         assert true;
      else
         assert false;

      if (s3.equalsIgnoreCase(s4))  // true
         assert true;
      else
         assert false;

      assert s1.compareTo(s2)==13; //true

      assert s2.compareTo(s1)==-13; //true

      assert s1.compareTo(s1)==0; //true

      assert s3.compareTo(s4)==-32; //true

      assert s4.compareTo(s3)==32; //true

      // test regionMatches (case sensitive)
      if (!s3.regionMatches(0, s4, 0, 5)) //true
         assert true;
      else
         assert false;

      // test regionMatches (ignore case)
      if (s3.regionMatches(true, 0, s4, 0, 5)) //true
         assert true;
      else
         assert false;
   }
}
