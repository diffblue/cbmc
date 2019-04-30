public class test_intern
{
    public static void testPass()
    {
        // Arrange
        String s1 = "abc";
        String s2 = "abc";
        // Act
        String x = s1.intern();
        String y = s2.intern();
        // Assert
        assert(x == y);
    }

    public static void testFail()
    {
        // Arrange
        String s1 = "abc";
        String s2 = "abd";
        // Act
        String x = s1.intern();
        String y = s2.intern();
        // Assert
        assert(x == y);
   }
}
