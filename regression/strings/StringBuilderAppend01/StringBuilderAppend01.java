public class StringBuilderAppend01
{
   public static void main(String[] args)
   {
      Object objectRef = "diffblue";
      String string = "test";
      char[] charArray = {'v', 'e', 'r', 'i', 'f', 'i', 'c', 'a', 't', 'i', 'o', 'n'};
      boolean booleanValue = true;
      char characterValue = 'Z';
      int integerValue = 7;
      long longValue = 10000000000L;
      float floatValue = 2.5f;
      double doubleValue = 33.333;

      StringBuilder lastBuffer = new StringBuilder("last buffer");
      StringBuilder buffer = new StringBuilder();

      buffer.append(objectRef)
            .append("%n")
            .append(string)
            .append("%n")
            .append(charArray)
            .append("%n")
            .append(charArray, 0, 3)
            .append("%n")
            .append(booleanValue)
            .append("%n")
            .append(characterValue)
            .append("%n")
            .append(integerValue)
            .append("%n")
            .append(longValue)
            .append("%n")
            .append(floatValue)
            .append("%n")
            .append(doubleValue)
            .append("%n")
            .append(lastBuffer);

      String tmp=buffer.toString();
      assert tmp.equals("diffblue%ntest%nverification%nver%ntrue%nZ%n7%n10000000000%n2.5%n33.333%nlast buffer");
   }
}
