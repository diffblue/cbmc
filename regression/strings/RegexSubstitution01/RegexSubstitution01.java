import java.util.Arrays;

public class RegexSubstitution01
{
   public static void main(String[] args)
   {
      String firstString = "Diffblue ***";
      String secondString = "Automatic Test Case Generation";

      firstString = firstString.replaceAll("\\*", "^");

      assert firstString.equals("Diffblue ^^^");

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

      assert secondString.equals("automatedautomatedautomatedAutomated Test Case Generation");

      System.out.print("String split at commas: ");
      String[] results = secondString.split(" \\s*");
      System.out.println(Arrays.toString(results));
      assert results[0].equals("automatedautomatedautomatedAutomated");
      assert results[1].equals("Test");
      assert results[2].equals("Case");
      assert results[3].equals("Generation");
   }
}
