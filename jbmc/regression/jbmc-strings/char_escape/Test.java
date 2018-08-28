public class Test {

    public static boolean test(char c1, char c2, char c3, char c4, char c5, char c6, char c7, char c8) {
        StringBuilder sb = new StringBuilder("");
        sb.append(c1);
        sb.append(c2);
        sb.append(c3);
        sb.append(c4);
        sb.append(c5);
        sb.append(c6);
        sb.append(c7);
        sb.append(c8);
        if (sb.toString().equals("\b\t\n\f\r\"\'\\")) {
            assert false;
            return true;
        }
        if (!sb.toString().equals("\b\t\n\f\r\"\'\\")) {
            assert false;
            return false;
        }
        assert false;
        return true;
    }
}
