public class Test {

    public static String check(String[] array) {
        // Filter
        if(array == null)
            return "null array";
        if(array.length < 2)
            return "too short";
        if(array[0] == null)
            return "null string";

        // Arrange
        String s0 = array[0];
        String s1 = array[1];

        // Act
        boolean b = s0.equals(s1);

        // Assert
        assert(s0 != null);
        assert(!b);

        // Return
        return s0 + s1;
    }
}
