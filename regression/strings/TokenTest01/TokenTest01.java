import java.util.StringTokenizer;

public class TokenTest01
{
   public static void main(String[] args)
   {
      String sentence = "automatic test case generation";
      String[] tokens = sentence.split(" ");
      System.out.printf("Number of elements: %d\nThe tokens are:\n",
         tokens.length);
      assert tokens.length==4;

      int i=0;
      for (String token : tokens)
      {
         System.out.println(token);
         if (i==0) assert token.equals("automatic");
         else if (i==1) assert token.equals("test");
         else if (i==2) assert token.equals("case");
         else if (i==3) assert token.equals("generation");
         ++i;
      }
   }
}
