public class Cart {

    class Product {
        public String size;
        public Category cat;
    }

    class Category {
        public String name;
    }

    public boolean checkTax4(Product product, String s) {
        product.size="abc";
        return s.startsWith(product.cat.name);
    }
}
