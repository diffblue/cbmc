public class Test {

    public static void testMe(String input, int radix) {

        // Railroad the solver a bit to speed up solving
        // (note use of > and < to dodge constant propagation)
        if(input == null || input.length() != 1 || input.charAt(0) != 'k' || radix < 30 || radix > 30)
            return;

	int value = Integer.parseInt(input, radix);
	if(value == 20)
	    assert false;
        else
            assert false;

    }

}
