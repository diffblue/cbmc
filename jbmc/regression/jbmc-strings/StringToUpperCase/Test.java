public class Test {
    public String det()
    {
        StringBuilder builder = new StringBuilder();
        builder.append("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toLowerCase());
        builder.append("abcdeghijklmnopfrstuqwxyzABCDvFGHIJKLMENOPQRSTUVWXYZ".toUpperCase());
        builder.append("abcdeghijlmnopqrstvwxyzABCDEFGHIJuKLMNOPQRSfkTUVWXYZ".toUpperCase());
        builder.append("acdefghijklmnopqrsuvwxyzABCDEFbGHIJKLMNOPtQRSTUVWXYZ".toUpperCase());
        builder.append("abcdfghijklmnopqrstuvwxyzABCDEFGHIJeKLMNOPQRSTUVWXYZ".toUpperCase());
        String result = builder.toString();
        assert result.length() < 5;
        return result;
    }

    public String nonDet(String s)
    {
        if(s.length() < 20)
            return "Short string";
        if(!s.startsWith("a"))
            return "String not starting with a";

        StringBuilder builder = new StringBuilder();
        builder.append(s.toUpperCase());
        builder.append(s.toUpperCase());
        builder.append(":");
        builder.append(s);
        builder.append(":");
        builder.append(s.toUpperCase());
        builder.append(s.toUpperCase());
        String result = builder.toString();
        assert result.length() < 5;
        return result;
    }

    public String withDependency(String s, boolean b)
    {
        // Filter
        if(s == null || s.length() < 20)
            return "Short string";
        if(!s.endsWith("a"))
            return "String not ending with a";

        // Act
        String result = s + s.toUpperCase();

        // Assert
        if(b) {
            assert(result.endsWith("A"));
        } else {
            assert(!result.endsWith("A"));
        }
        return result;
    }
}
