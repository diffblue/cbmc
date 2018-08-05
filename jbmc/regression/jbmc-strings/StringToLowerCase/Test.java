public class Test {
    public String det()
    {
        StringBuilder builder = new StringBuilder();
        builder.append("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toLowerCase());
        builder.append("abcdeghijklmnopfrstuqwxyzABCDvFGHIJKLMENOPQRSTUVWXYZ".toLowerCase());
        builder.append("abcdeghijlmnopqrstvwxyzABCDEFGHIJuKLMNOPQRSfkTUVWXYZ".toLowerCase());
        builder.append("acdefghijklmnopqrsuvwxyzABCDEFbGHIJKLMNOPtQRSTUVWXYZ".toLowerCase());
        builder.append("abcdfghijklmnopqrstuvwxyzABCDEFGHIJeKLMNOPQRSTUVWXYZ".toLowerCase());
        String result = builder.toString();
        assert result.length() < 5;
        return result;
    }

    public String nonDet(String s)
    {
        if(s.length() < 20)
            return "Short string";
        if(!s.startsWith("A"))
            return "String not starting with A";

        StringBuilder builder = new StringBuilder();
        builder.append(s.toLowerCase());
        builder.append(s.toLowerCase());
        builder.append(":");
        builder.append(s);
        builder.append(":");
        builder.append(s.toLowerCase());
        builder.append(s.toLowerCase());
        String result = builder.toString();
        assert result.length() < 5;
        return result;
    }

    public String withDependency(String s, boolean b)
    {
        // Filter
        if(s == null || s.length() < 20)
            return "Short string";
        if(!s.endsWith("A"))
            return "String not ending with A";

        // Act
        String result = s + s.toLowerCase();

        // Assert
        if(b) {
            assert(result.endsWith("a"));
        } else {
            assert(!result.endsWith("a"));
        }
        return result;
    }
}
