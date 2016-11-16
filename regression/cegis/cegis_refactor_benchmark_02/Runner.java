class DoubleWrapper {
  public double value;

  @Override
  public boolean equals(Object o) {
    DoubleWrapper tmpDoubleWrapper = (DoubleWrapper) o;
    return value == tmpDoubleWrapper.value;
  }
}

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
void sale(ITaxCalculator calc, DoubleWrapper price) {
  if (calc != null)
    price.value = calc.addTaxes(price.value);
}
void print(ITaxCalculator calc, DoubleWrapper price) {
  DoubleWrapper percentage = new DoubleWrapper();
  if (calc == null)
    percentage.value=0;
  else
    percentage.value=calc.addTaxes(100.0) - 100.0;
  
  System.out.print("Tax rate: ");
  System.out.print(percentage.value);
  System.out.println('%');
}
}