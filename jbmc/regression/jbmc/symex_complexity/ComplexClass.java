import java.util.*;

public class ComplexClass {

    public void loopBlacklist(List<String> prop, int increment, int size) {
        while (size <= 1000)
        {
            if (size > 500)
                branchCancel(prop, increment, size);

            size++;
        }
    }

    public void branchCancel(List<String> prop, int increment, int size) {
        StringBuilder sb = new StringBuilder();
        for (String str : prop)
        {
            if (size >= 50)
                sb.append(str);

            size+=increment;
        }
    }

    private static Properties properties = new Properties();

    public void process(Properties prop) {

        properties = prop;

        for (Enumeration<?> pe = properties.propertyNames(); pe.hasMoreElements(); )
        {
            String key = (String)pe.nextElement();
            String value = recurse(key, properties.getProperty(key), 1);
            if (value != null)
            {
                properties.setProperty(key, value);
            }
        }
    }

    private static String recurse(String key, String value, int level)
    {
        if (level > 9)
            throw new IllegalArgumentException("Recursion level too deep.");

        int from = 0;
        StringBuffer result = null;
        while (from < value.length()) {
            while (from < value.length()) {
                int start = value.indexOf("[", from);
                if (start >= 0) {
                    int end = value.indexOf(']', start);
                    if (end < 0) {
                        break;
                    }
                    String var = value.substring(start + 1, end);
                    if (result == null) {
                        result = new StringBuffer(value.substring(from, start));
                    } else {
                        result.append(value.substring(from, start));
                    }
                    if (properties.containsKey(var)) {
                        String val = recurse(var, properties.getProperty(var), level + 1);
                        if (val != null) {
                            result.append(val);
                            properties.setProperty(var, val);
                        } else {
                            result.append((properties.getProperty(var)).trim());
                        }
                    }

                    from = end + 1;
                } else {
                    break;
                }
            }
        }

        if (result != null && from < value.length())
        {
            result.append(value.substring(from));
        }
        return (result == null) ? null : result.toString();
    }
}
