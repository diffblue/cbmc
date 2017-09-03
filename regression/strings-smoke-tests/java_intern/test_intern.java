public class test_intern
{
   public static void main(/*String[] argv*/)
   {
      String s1 = "abc";
      String s3 = "abc";
      String x = s1.intern();
      String y = s3.intern();
      assert(x == y);
   }
}
