public class test
{
    public static void nondet(String stringArg)
    {
        StringBuilder sb = new StringBuilder(stringArg);
        sb.append("Z");
        String s = sb.toString();
        if (s.startsWith("fg")) {
            assert false;
        } else if (s.endsWith("Z")) {
            assert false;
        } else {
            assert false;
        }
    }
}
