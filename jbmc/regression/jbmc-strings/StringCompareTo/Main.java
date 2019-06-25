class Main {

    public static void nondetPass(String s1, String s2) {
        if (s1.startsWith("abc") && s2.startsWith("cde")) {
            assert s1.compareTo(s2) == -2;   // assertion.1 true
            assert s2.compareTo(s1) == 2;    // assertion.2 true
        } else if (s1.startsWith("abc") && s1.length() == 3 && s2.startsWith("abc") && s2.length() > 3) {
            assert s1.compareTo(s2) < 0;     // assertion.3 true
            assert s2.compareTo(s1) > 0;     // assertion.4 true
        } else if (s1.startsWith("abc") && s1.length() == 3 && s2.startsWith("abc") && s2.length() == 3) {
            assert s1.compareTo(s2) == 0;    // assertion.5 true
            assert s2.compareTo(s1) == 0;    // assertion.6 true
        }
    }

    public static void nondetFail(boolean b, String s1, String s2) {
        if (s1.startsWith("abc") && s2.startsWith("cde")) {
            if (b)
                assert s1.compareTo(s2) != -2;   // assertion.1 false
            else
                assert s2.compareTo(s1) != 2;    // assertion.2 false
        } else if (s1.startsWith("abc") && s1.length() == 3 && s2.startsWith("abc") && s2.length() > 3) {
            if (b)
                assert s1.compareTo(s2) >= 0;    // assertion.3 false
            else
                assert s2.compareTo(s1) <= 0;    // assertion.4 false
        } else if (s1.startsWith("abc") && s1.length() == 3 && s2.startsWith("abc") && s2.length() == 3) {
            if (b)
                assert s1.compareTo(s2) != 0;    // assertion.5 false
            else 
                assert s2.compareTo(s1) != 0;    // assertion.6 false
        } 
    }

}
