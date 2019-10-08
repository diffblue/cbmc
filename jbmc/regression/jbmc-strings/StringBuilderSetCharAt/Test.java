public class Test {
    public String nondetChoice(boolean choice)
    {
        String s =
          choice ? "abcdefghijklmnopqrstuvwxyz" : "bbcdefghijklmnopqrstuvwxyz";
        StringBuilder builder = new StringBuilder(s);
        builder.setCharAt(3, '!');
        builder.setCharAt(5, '!');
        builder.setCharAt(7, '!');
        builder.setCharAt(9, '!');
        builder.setCharAt(13, '!');
        builder.setCharAt(15, '!');
        builder.setCharAt(17, '!');
        builder.setCharAt(19, '!');
        builder.setCharAt(4, ':');
        builder.setCharAt(5, ':');
        builder.setCharAt(6, ':');
        builder.setCharAt(9, ':');
        builder.setCharAt(10, ':');
        builder.setCharAt(11, ':');
        builder.setCharAt(16, ':');
        builder.setCharAt(18, ':');
        String result = builder.toString();
        assert result.length() < 5;
        return result;
    }

    public String nonDet(String s, char c, int i)
    {
        StringBuilder builder = new StringBuilder(s);
        if(i + 5 >= s.length() || 19 >= s.length() || i < 0)
            return "Out of bounds";
        builder.setCharAt(i, c);
        builder.setCharAt(i+5, 'x');
        builder.setCharAt(7, '!');
        builder.setCharAt(9, '!');
        builder.setCharAt(13, '!');
        builder.setCharAt(15, '!');
        builder.setCharAt(17, '!');
        builder.setCharAt(19, '!');
        builder.setCharAt(4, ':');
        builder.setCharAt(5, ':');
        builder.setCharAt(6, c);
        builder.setCharAt(9, ':');
        builder.setCharAt(10, ':');
        builder.setCharAt(11, ':');
        builder.setCharAt(16, ':');
        builder.setCharAt(18, ':');
        String result = builder.toString();
        assert result.length() < 5;
        return result;
    }

    public String withDependency(boolean b, boolean choice)
    {
        String s =
          choice ? "abcdefghijklmnopqrstuvwxyz" : "abcdefghijklmnopqrstuvwxyy";
        StringBuilder builder = new StringBuilder(s);
        builder.setCharAt(3, '!');
        builder.setCharAt(5, '!');

        if(b) {
            assert builder.toString().startsWith("abc!");
        } else {
            assert !builder.toString().startsWith("abc!");
        }
        return builder.toString();
    }

}
