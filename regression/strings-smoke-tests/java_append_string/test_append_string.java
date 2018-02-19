public class test_append_string
{
    public static void main()
    {
        String di = new String("di");
        StringBuilder diff = new StringBuilder();
        diff.append(di);
        diff.append("ff");
        System.out.println(diff);
        String s = diff.toString();
        System.out.println(s);
        assert s.equals("diff");
    }

    public static void check(StringBuilder sb, String str)
    {
        String init = sb.toString();
        if(str.length() >= 4)
        {
            org.cprover.CProverString.append(sb, str, 2, 4);
            String res = sb.toString();
            assert(res.startsWith(init));
            assert(res.endsWith(org.cprover.CProverString.substring(str, 2, 4)));
            assert(res.length() == init.length() + 2);
            assert(!res.equals("foobarfuz"));
        }
    }

}
