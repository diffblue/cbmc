public class StaticCharMethods02
{
   public static void main(String[] args)
   {
      char c = 0;
      assert Character.toUpperCase(c)!=Character.toLowerCase(c);
   }
}
