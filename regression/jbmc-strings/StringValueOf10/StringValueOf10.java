public class StringValueOf10
{
   public static void main(String[] args)
   {
      Object objectRef = "test"; // assign string to an Object reference
      String tmp=String.valueOf(objectRef);
      assert tmp.equals("tesst");
   }
}
