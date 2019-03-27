// This test uses CProverString so should be compiled with
// javac Test.java ../cprover/CProverString.java

class Test {
    public void testSuccess(String s, int start, int end) {
        // Filter
        if (s == null)
            return;

        // Act
        String sub = org.cprover.CProverString.substring(s, start, end);

        // Arrange
        StringBuilder reference = new StringBuilder();
        if(start < 0)
            start = 0;
        for (int i = start; i < end && i < s.length(); i++)
            reference.append(org.cprover.CProverString.charAt(s, i));

        // Assert
        assert sub.equals(reference.toString());
    }

    public void testFail(int i) {
        // Arrange
        String[] s = new String[5];

        // Act
        s[0] = org.cprover.CProverString.substring("foo", 0, 1);
        s[1] = org.cprover.CProverString.substring("foo", 0, 4);
        s[2] = org.cprover.CProverString.substring("foo", -1, 0);
        s[3] = org.cprover.CProverString.substring("foo", -10, -1);
        s[4] = org.cprover.CProverString.substring("foo", -10, 25);

        // Assert
        if(i == 0)
            assert !s[0].equals("f");
        if(i == 1)
            assert !s[1].equals("foo");
        if(i == 2)
            assert !s[2].equals("");
        if(i == 3)
            assert !s[3].equals("");
        if(i == 4)
            assert !s[4].equals("foo");
    }

    public void testNull(String s, int start, int end) {
        // Check that the CProverString version excludes the null case
        String sub = org.cprover.CProverString.substring(s, start, end);
    }

}
