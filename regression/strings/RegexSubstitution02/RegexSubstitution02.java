import java.util.Arrays;

public class RegexSubstitution02
{
   public static void main(String[] args)
   {
      String firstString = "Diffblue ***";
      String secondString = "Automatic Test Case Generation";

      firstString = firstString.replaceAll("\\*", "^");

      secondString = secondString.replaceAll("Automatic", "Automated");

      System.out.printf(
         "\"Automatic\" substituted for \"Automated\": %s\n", secondString);
      secondString.equals("Automated Test Case Generation");

      System.out.printf("Every word replaced by \"word\": %s\n\n",
         firstString.replaceAll("\\w+", "word"));

      System.out.printf("Original String 2: %s\n", secondString);
      secondString.equals("Automated Test Case Generation");

      for (int i = 0; i < 3; i++)
         secondString = secondString.replaceFirst("\\A", "automated");

      System.out.print("String split at commas: ");
      String[] results = secondString.split(" \\s*");
      System.out.println(Arrays.toString(results));
      assert results[0].equals("automatedautomatedautomatedaAutomated");
   }
}
