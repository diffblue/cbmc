public class StringBuilderInsertDelete03
{
   public static void main(String[] args)
   {
      Object objectRef = "diffblue";
      String string = "test";
      char[] charArray = {'v', 'e', 'r', 'i', 'f', 'i', 'c', 'a', 't', 'i', 'o', 'n'};
      boolean booleanValue = true;
      char characterValue = 'K';
      int integerValue = 7;
      long longValue = 10000000;
      float floatValue = 2.5f;
      double doubleValue = 33.333;

      StringBuilder buffer = new StringBuilder();

      buffer.insert(0, objectRef)
            .insert(0, "-")
            .insert(0, string)
            .insert(0, "-")
            .insert(0, charArray)
            .insert(0, "-")
            .insert(0, charArray, 3, 3)
            .insert(0, "-")
            .insert(0, booleanValue)
            .insert(0, "-")
            .insert(0, characterValue)
            .insert(0, "-")
            .insert(0, integerValue)
            .insert(0, "-")
            .insert(0, longValue)
            .insert(0, "-")
            .insert(0, floatValue)
            .insert(0, "-")
            .insert(0, doubleValue);

      buffer.deleteCharAt(10);
      buffer.delete(2, 6);

      String tmp=buffer.toString();
      assert tmp.equals("33-2.510000000-7-K-true-iai-verification-test-diffblue");
   }
}
