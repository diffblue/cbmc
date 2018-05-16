public class Test_hex
{
    public static void main(boolean b)
    {
        String str = new String("+00AbCdEf0123");
        long parsed = Long.parseLong(str, 16);
        if (b) {
            assert(parsed == 737894400291L);
        }
        else {
            assert(parsed != 737894400291L);
        }
    }
}
