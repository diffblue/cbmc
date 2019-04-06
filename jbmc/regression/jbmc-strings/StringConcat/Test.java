public class Test {

    public String stringDet() {
        String s = "a";
        s += "b";
        s += "c";
        s += "d";
        s += "e";
        s += "f";
        s += "g";
        s += "h";
        s += "i";
        s += "j";
        s += "k";
        s += "l";
        s += "m";

        assert(false);
        return s;
    }

    public String stringNonDet(String arg) {
        String s = arg;
        s += "b";
        s += "c";
        s += "d";
        s += "e";
        s += "f";
        s += arg;
        s += "h";
        s += "i";
        s += "j";
        s += "k";
        s += "l";
        s += arg;

        assert(false);
        return s;
    }

    public String bufferDet() {
        StringBuffer s = new StringBuffer();
        s.append("a");
        s.append("b");
        s.append("c");
        s.append("d");
        s.append("e");

        s.append("a");
        s.append("b");
        s.append("c");
        s.append("d");
        s.append("e");

        s.append("a");
        s.append("b");
        s.append("c");
        s.append("d");
        s.append("e");

        s.append("a");
        s.append("b");
        s.append("c");
        s.append("d");
        s.append("e");

        s.append("a");
        s.append("b");
        s.append("c");
        s.append("d");
        s.append("e");

        s.append("a");
        s.append("b");
        assert(false);
        return s.toString();
    }

    public String charBufferDet() {
        StringBuffer s = new StringBuffer();
        s.append('a');
        s.append('b');
        s.append('c');
        s.append('d');
        s.append('e');

        s.append('a');
        s.append('b');
        s.append('c');
        s.append('d');
        s.append('e');

        s.append('a');
        s.append('b');
        s.append('c');
        s.append('d');
        s.append('e');

        s.append('a');
        s.append('b');
        s.append('c');
        s.append('d');
        s.append('e');

        s.append('a');
        s.append('b');
        s.append('c');
        s.append('d');
        s.append('e');

        s.append('a');
        s.append('b');

        assert(false);
        return s.toString();
    }

    public String charBufferDetLoop(int width) {
        if(width <= 5)
            return "";
        StringBuffer sb = new StringBuffer();
        sb.append('+');
        for(int i=1; i < width-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');
        sb.append('|');

        sb.append(' ');
        sb.append('c');
        int padding = width - 2;
        while(padding-- > 0)
            sb.append(' ');

        sb.append(' ');
        sb.append('|');
        sb.append('\n');
        assert(false);
        return sb.toString();
    }

    public String charBufferDetLoop2(int width, int height) {
        if(width <= 0 || height <= 0)
            return "";
        StringBuffer sb = new StringBuffer();
        sb.append('+');
        for(int i=1; i < width-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');
        sb.append('|');

        sb.append(' ');
        sb.append('c');
        int padding = width - 2;
        while(padding-- > 0)
            sb.append(' ');
        sb.append(' ');
        sb.append('|');
        sb.append('\n');

        sb.append('+');
        for(int i=1; i<width; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');

        for(int i = 0; i < height; ++i) {
            sb.append('|');
            sb.append(' ');
            sb.append('d');
            padding = width - 3;
            while(padding-- > 0)
                sb.append(' ');
            sb.append(' ');
            sb.append('|');
            sb.append('\n');
        }

        sb.append('+');
        for(int i=1; i<width-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');

        assert(false);
        return sb.toString();
    }

    public String bufferNonDetLoop(int width, String s) {
        if(width <= 5 || s.length() >= width || s.length() == 0)
            return "";
        StringBuffer sb = new StringBuffer();
        sb.append('+');
        for(int i=1; i < width-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');
        sb.append('|');

        sb.append(' ');
        sb.append(s);
        int padding = width - s.length();
        while(padding-- > 0)
            sb.append(' ');
        sb.append(' ');
        sb.append('|');
        sb.append('\n');

        assert(false);
        return sb.toString();
    }

    public String bufferNonDetLoop2(int width, String c) {
        if(width < 5 || c.length() > width)
            return "";

        StringBuffer sb = new StringBuffer();
        sb.append('+');

        for(int i=1; i<width-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');
        sb.append('|');
        for(int i = 0; i < width; ++i) {
            sb.append(' ');
            sb.append(c);
            int padding = width - c.length();
            while(padding-- > 0)
                sb.append(' ');
            sb.append(' ');
            sb.append('|');
        }
        sb.append('\n');

        assert(false);
        return sb.toString();
    }

    public String bufferNonDetLoop3(int cols, int columnWidth, String c) {
        StringBuffer sb = new StringBuffer();
        sb.append('-');
        for(int i = 0; i < cols; ++i)
            sb.append(c);

        assert(false);
        return sb.toString();
    }
    public String bufferNonDetLoop4(int cols, int columnWidth, String c) {
        StringBuffer sb = new StringBuffer();
        for(int i=1; i < columnWidth-1; ++i)
            sb.append('-');
        for(int i = 0; i < cols; ++i) {
            sb.append(c);
        }

        assert(false);
        return sb.toString();
    }

    public String bufferNonDetLoop5(int cols, int columnWidth, String c, String data[]) {
        if(cols<1)
            return "";

        StringBuffer sb = new StringBuffer();
        sb.append('+');
        int totalWidth = columnWidth * cols;
        for(int i=1; i<totalWidth-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');
        sb.append('|');
        for(int i = 0; i < cols; ++i) {
            sb.append(' ');
            sb.append(c);
            int padding = columnWidth - c.length();
            while(padding-- > 0)
                sb.append(' ');
            sb.append(' ');
            sb.append('|');
        }
        sb.append('\n');

        sb.append('+');
        for(int i=1; i<totalWidth-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');

        for(int i = 0; i < data.length; ++i) {
            sb.append('|');
            String d = data[i];
            sb.append(' ');
            sb.append(d);
            int padding = columnWidth - d.length();
            while(padding-- > 0)
                sb.append(' ');
            sb.append(' ');
            sb.append('|');

            if(i % cols == 0)
                sb.append('\n');
        }

        sb.append('+');
        for(int i=1; i<totalWidth-1; ++i)
            sb.append('-');
        sb.append('+');
        sb.append('\n');

        assert(false);
        return sb.toString();
    }

    static boolean fromNonDetArray(String[] argv)
    {
        String s = argv[0];
        String u = s.concat("llo");
        if(u.equals("Hello")) {
            return true;
        }
        return false;
    }

}
