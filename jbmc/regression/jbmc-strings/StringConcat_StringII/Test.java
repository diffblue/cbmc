// This test uses CProverString so should be compiled with
// javac Test.java ../cprover/CProverString.java
import org.cprover.CProverString;

class Test {
    public void testSuccess(String s, String t, int start, int end) {
        // Filter
        if (s == null || t == null)
            return;

        // Act
        StringBuilder sb = new StringBuilder(s);
        String result = CProverString.append(sb, t, start, end).toString();

        // Arrange
        StringBuilder reference = new StringBuilder(s);
        if(start < 0)
            start = 0;
        for (int i = start; i < end && i < t.length(); i++)
            reference.append(org.cprover.CProverString.charAt(t, i));

        // Assert
        assert result.equals(reference.toString());
    }

    public void testFail(int i) {
        // Arrange
        StringBuilder sb = new StringBuilder("foo");

        // Act
        CProverString.append(sb, "bar", 0, 1);
        CProverString.append(sb, "bar", 0, 4);
        CProverString.append(sb, "foo", -1, 0);
        CProverString.append(sb, "foo", -10, -1);
        CProverString.append(sb, "bar", -10, 25);

        // Assert
        assert !sb.toString().equals("foobbarbar");
    }
}
