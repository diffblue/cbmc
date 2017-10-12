public class test_hash_code
{
   public static void main(/*String[] argv*/)
   {
      String s1 = "ab";
      String s2 = "ab";
      assert(s1.hashCode() != s2.hashCode());
   }
}
