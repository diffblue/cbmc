public class StringValueOf01
{
   public static void main(String[] args)
   {
      char[] charArray = {'d', 'i', 'f', 'f', 'b', 'l', 'u', 'e'};
      boolean booleanValue = false;
      char characterValue = 'T';
      int integerValue = 7;
      long longValue = 10000000000L; // L suffix indicates long
      float floatValue = 2.5f; // f indicates that 2.5 is a float
      double doubleValue = 33.333; // no suffix, double is default
      Object objectRef = "test"; // assign string to an Object reference

      String tmp=String.valueOf(charArray);
      assert tmp.equals("diffblue");

      tmp=String.valueOf(charArray, 3, 3);
      assert tmp.equals("fbl");

      tmp=String.valueOf(booleanValue);
      assert tmp.equals("false");

      tmp=String.valueOf(characterValue);
      assert tmp.equals("T");

      tmp=String.valueOf(integerValue);
      assert tmp.equals("7");

      tmp=String.valueOf(longValue);
      assert tmp.equals("10000000000");

      tmp=String.valueOf(floatValue);
      assert tmp.equals("2.5");

      tmp=String.valueOf(doubleValue);
      assert tmp.equals("33.333");

      tmp=String.valueOf(objectRef);
      assert tmp.equals("test");
   }
}
