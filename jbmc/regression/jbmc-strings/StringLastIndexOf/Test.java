public class Test {
    int fromIndex;

    public void check(String input_String1, String input_String2, int i) {
        if(input_String1 != null && input_String2 != null) {
            if (i == 0) {
                // The last occurrence of the empty string "" is considered to
                // occur at the index value this.length()
                int lio = input_String1.lastIndexOf(input_String2);
                if (input_String2.length() == 0)
                    assert lio == input_String1.length();
            } else if (i == 1) {
                // Contradiction with the previous condition (should fail).
                assert "foo".lastIndexOf("") != 3;
            } else if (i == 2 && input_String2.length() > 0) {
                int lio = input_String1.lastIndexOf(org.cprover.CProverString.charAt(input_String2, 0), fromIndex);
                if (input_String2.length() == 0)
                    assert lio == fromIndex;
            } else if (i == 3) {
                assert "foo".lastIndexOf("", 2) != 2;
            }
        }
    }
}
