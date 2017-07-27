public class Test
{
    public static void foo(int i)
    {
        if (i == 1) {
            String str1 = new String("F");
            int parsed1 = Integer.parseInt(str1, 16);
            assert(parsed1 == 15);
            assert(parsed1 != 15);
        }
        else if (i == 2) {
            String str2 = new String("123");
            int parsed2 = Integer.parseInt(str2, 10);
            assert(parsed2 == 123);
            assert(parsed2 != 123);
        }
        else if (i == 3) {
            String str3 = new String("77");
            int parsed3 = Integer.parseInt(str3, 8);
            assert(parsed3 == 63);
            assert(parsed3 != 63);
        }
        else if (i == 4) {
            String str4 = new String("-101");
            int parsed4 = Integer.parseInt(str4, 2);
            assert(parsed4 == -5);
            assert(parsed4 != -5);
        }
        else if (i == 5) {
            String str5 = new String("00aB");
            int parsed5 = Integer.parseInt(str5, 16);
            assert(parsed5 == 171);
            assert(parsed5 != 171);
        }
    }
}
