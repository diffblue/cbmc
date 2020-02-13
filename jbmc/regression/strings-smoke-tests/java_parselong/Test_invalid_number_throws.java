public class Test_invalid_number_throws
{
    public static void main(String input_string)
    {
      // Make test outputs readable by constraining length:
      if(input_string.length() != 4)
        return;
      long check = Long.parseLong(input_string);
      boolean pass1 = false, pass2 = false, pass3 = false, throw1 = false, throw2 = false, throw3 = false;
      // If we get here input_string should be validated, so parsing again shouldn't throw:
      try {
        Long.parseLong(input_string);
        pass1 = true;
      }
      catch(NumberFormatException e) {
        throw1 = true;
      }
      // Make it invalid:
      String broken = input_string + "&";
      try {
        Long.parseLong(broken);
        pass2 = true;
      }
      catch(NumberFormatException e) {
        throw2 = true;
      }
      // Make it valid again:
      String fixed = broken.substring(0, broken.length() - 1);
      try {
        Long.parseLong(fixed);
        pass3 = true;
      }
      catch(NumberFormatException e) {
        throw3 = true;
      }

      // Check we followed the expected path:
      assert(pass1 && throw2 && pass3 && !throw1 && !pass2 && !throw3);
      // Check we can get to the end at all:
      assert(false);
    }
}
