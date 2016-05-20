public class enum1 { 

    public enum Name { 
        ASCII(1, String.class),
        BIGINT(2, Long.class),
        BOOLEAN(3, Boolean.class),
        COUNTER(4, Long.class);
 
        final int protocolId;
        final Class<?> javaType;

        private Name(int protocolId, Class<?> javaType) {
            this.protocolId = protocolId;
            this.javaType = javaType;
        }

    };

    public static void main(String args[]) { 
	int i = 0;
        for (Name t : Name.values()) { 
	  i += t.protocolId;
        } 
	
    } 
} 

