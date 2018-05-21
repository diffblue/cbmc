public class Validate02
{
   public static void main(String[] args)
   {
      String address = "ZZZ IIII AAAA 5689";
      String city = "Oxford";
      String state = "Oxfordshire";
      String zip = "OX37AF";
      String phone = "+4477777";

      if (!ValidateInput02.validateAddress(address))
  		 assert false;
      else if (!ValidateInput02.validateCity(city))
         System.out.println("Invalid city");
      else if (!ValidateInput02.validateState(state))
         System.out.println("Invalid state");
      else if (!ValidateInput02.validateZip(zip))
         System.out.println("Invalid zip code");
      else
         System.out.println("Valid input.  Thank you.");
   }
}
