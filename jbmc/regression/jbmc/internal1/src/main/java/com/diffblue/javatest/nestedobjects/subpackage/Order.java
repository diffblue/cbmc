package com.diffblue.javatest.nestedobjects.subpackage;

public class Order {
  public Item item;

  /**
   * Checks if this order has an item.
   */
  public boolean hasItem() {
    if (item == null) {
      return false;
    } else {
      return true;
    }
  }

  /**
   * Sets the item for this order.
   */
  public boolean setItem(Item item) {
    boolean exists = hasItem();
    this.item = item;

    assert this.item == null;
    return exists;
  }
}
