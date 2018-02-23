public class Test {

    static void checkMaxInputLength(String arg1, String arg2) {
        // Filter
        if (arg1 == null || arg2 == null)
            return;

        // The validity of this depends on string-max-input-length
        assert arg1.length() + arg2.length() < 1_000_000;
    }

    static void checkMaxLength(String arg1, String arg2) {
        // Filter
        if (arg1 == null || arg2 == null)
            return;

        if(arg1.length() + arg2.length() < 4_001)
            return;

        // Act
        String s = arg1.concat(arg2);

        // When string-max-length is smaller than 4_000 this will
        // always be the case
        assert org.cprover.CProverString.charAt(s, 4_000) == '?';
    }

    static void main(String argv[]) {
        // Filter
        if (argv.length < 2)
            return;

        // Act
        checkMaxInputLength(argv[0], argv[1]);
        checkMaxLength(argv[0], argv[1]);
    }
}
