// This test uses CProverString so should be compiled with
// javac Test.java ../cprover/CProverString.java

public class Test {

    public boolean check(String input_String, char input_char, int input_int) {
        // Verify indexOf is conform to its specification
        int i = input_String.indexOf(input_char, input_int);

        assert i < input_String.length();

        int lower_bound;
        if (input_int < 0)
            lower_bound = 0;
        else
            lower_bound = input_int;

        if (i == -1) {
            for (int j = lower_bound; j < input_String.length(); j++)
                assert org.cprover.CProverString.charAt(input_String, j) != input_char;
        } else {
            assert i >= lower_bound;
            assert org.cprover.CProverString.charAt(input_String, i) == input_char;

            for (int j = lower_bound; j < i; j++)
                assert org.cprover.CProverString.charAt(input_String, j) != input_char;
        }
        return true;
    }

    public boolean check2() {
        // Verification should fail, this is to check the solver does
        // not get a contradiction
        int i = "hello".indexOf('o', 1);
        assert i == 4;
        i = "hello".indexOf('h', 1);
        assert i == -1;
        i = "hello".indexOf('e', 4);
        assert i == -1;
        i = "hello".indexOf('e', 8);
        assert i == -1;
        i = "hello".indexOf('x', 0);
        assert i == -1;
        i = "hello".indexOf('h', -1000);
        assert i == 0;
        assert false;
        return true;
    }
}
