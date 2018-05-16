import java.util.StringTokenizer;

public class TokenTest02
{
   public static void main(String[] args)
   {
      String sentence = "automatic test case generation";
      String[] tokens = sentence.split(" ");
 
      int i=0;
      for (String token : tokens)
      {
         if (i==3) assert token.equals("genneration");
         ++i;
      }
   }
}
