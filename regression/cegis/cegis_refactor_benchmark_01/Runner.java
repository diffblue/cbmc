interface ITaxCalculator {
  double addTaxes(double price);
}
class UsaTaxCalculator implements ITaxCalculator {
  public double addTaxes(double price) {
    return price * 1.25;
  }
}
class NullTaxCalculator implements ITaxCalculator {
  public double addTaxes(double price) {
    return price;
  }
}

public class Runner {
void sale(ITaxCalculator calc, double price) {
  if (calc != null)
    price = calc.addTaxes(price);
}
void print(ITaxCalculator calc, double price) {
  double percentage;
  if (calc == null)
    percentage=0;
  else
    percentage=calc.addTaxes(100.0) - 100.0;
  
  System.out.print("Tax rate: ");
  System.out.print(percentage);
  System.out.println('%');
}
}