
public class Test {
    public void check (int i) {
        if(i == 0)
        {
            // Arrange
            StringBuilder s = new StringBuilder("bar");

            // Act
            s = org.cprover.CProverString.insert(s, 0, "foo");

            // Should succeed
            assert s.toString().equals("foobar");

            // Should fail
            assert !s.toString().equals("foobar");
        }
        if(i == 1)
        {
            // Arrange
            StringBuilder s = new StringBuilder("bar");

            // Act
            s = org.cprover.CProverString.insert(s, -10, "foo");

            // Should succeed
            assert s.toString().equals("foobar");

            // Should fail
            assert !s.toString().equals("foobar");
        }
        if(i == 2)
        {
            // Arrange
            StringBuilder s = new StringBuilder("bar");

            // Act
            s = org.cprover.CProverString.insert(s, 10, "foo");

            // Should succeed
            assert s.toString().equals("barfoo");

            // Should fail
            assert !s.toString().equals("barfoo");
        }

    }
}
