public class Test
{
    public static String checkDet()
    {
        String tmp = String.valueOf(1000000);
        tmp = String.valueOf(1000001);
        tmp = String.valueOf(1000002);
        tmp = String.valueOf(1000003);
        tmp = String.valueOf(1000004);
        tmp = String.valueOf(1000005);
        tmp = String.valueOf(-1000001);
        tmp = String.valueOf(-1000002);
        tmp = String.valueOf(-1000003);
        tmp = String.valueOf(1000004);
        tmp = String.valueOf(1000005);
        tmp = String.valueOf(-1000001);
        tmp = String.valueOf(-1000002);
        tmp = String.valueOf(1000003);
        tmp = String.valueOf(1000004);
        tmp = String.valueOf(1000005);
        tmp = String.valueOf(1000001);
        tmp = String.valueOf(-1000002);
        tmp = String.valueOf(-1000003);
        tmp = String.valueOf(1000004);
        tmp = String.valueOf(1000005);
        assert tmp.length() < 5;
        return tmp;
    }

    public static String checkNonDet(int i)
    {
        String tmp = String.valueOf(1000000);
        tmp = String.valueOf(i + 1);
        tmp = String.valueOf(i + 2);
        tmp = String.valueOf(i + 3);
        tmp = String.valueOf(i + 4);
        tmp = String.valueOf(i + 5);
        tmp = String.valueOf(i - 1);
        tmp = String.valueOf(i - 2);
        tmp = String.valueOf(i - 3);
        tmp = String.valueOf(i - 4);
        tmp = String.valueOf(i - 5);
        tmp += " ";
        tmp += String.valueOf(i);
        tmp += " ";
        tmp += String.valueOf(i + 2);
        tmp += " ";
        tmp += String.valueOf(i + 3);
        tmp += " ";
        tmp += String.valueOf(-i);
        tmp += " ";
        tmp += String.valueOf(-i + 1);
        tmp += " ";
        tmp += String.valueOf(-i - 2);
        assert tmp.length() < 5;
        return tmp;
    }

    public static void checkWithDependency(boolean b)
    {
        String s = String.valueOf(12);
        if (b) {
            assert(s.startsWith("12"));
        }
        else {
            assert(!s.startsWith("12"));
        }
    }

}
