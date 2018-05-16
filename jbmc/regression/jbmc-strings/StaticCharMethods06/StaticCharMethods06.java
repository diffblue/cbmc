public class StaticCharMethods06
{
   public static void main(String[] args)
   {
      Character c1 = 'A';
      Character c2 = 'A';

      if (c1.equals(c2))
      {
         System.out.println("c1 and c2 are equal\n");
         assert true;
      }
      else
      {
         System.out.println("c1 and c2 are not equal\n");
         assert false;
      }
   }
}
