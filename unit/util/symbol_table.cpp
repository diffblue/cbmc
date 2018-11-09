/// Author: Diffblue Ltd.

/// \file Tests for symbol_tablet

#include <testing-utils/use_catch.h>
#include <util/exception_utils.h>
#include <util/journalling_symbol_table.h>

TEST_CASE("Iterating through a symbol table", "[core][utils][symbol_tablet]")
{
  symbol_tablet symbol_table;

  symbolt symbol;
  irep_idt symbol_name = "Test";
  symbol.name = symbol_name;

  symbol_table.insert(symbol);

  int counter = 0;
  for(auto &entry : symbol_table)
  {
    (void)entry; // we are just testing iteration here
    ++counter;
  }

  REQUIRE(counter == 1);
}

SCENARIO(
  "symbol_table_validity_checks",
  "[core][utils][symbol_table_validity_checks]")
{
  GIVEN("A valid symbol table")
  {
    symbol_tablet symbol_table;

    symbolt symbol;
    irep_idt symbol_name = "Test_TestBase";
    symbol.name = symbol_name;
    symbol.base_name = "TestBase";
    symbol.module = "TestModule";
    symbol.mode = "C";

    symbol_table.insert(symbol);

    THEN("validate() should return")
    {
      symbol_table.validate(validation_modet::EXCEPTION);
    }
    WHEN("A symbol name is transformed without updating the symbol table")
    {
      symbolt &transformed_symbol = symbol_table.get_writeable_ref(symbol_name);
      transformed_symbol.name = "TransformTest";

      THEN("validate() should throw an exception")
      {
        REQUIRE_THROWS_AS(
          symbol_table.validate(validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
      // Reset symbol to a valid name after the previous test
      transformed_symbol.name = symbol_name;
    }
    WHEN(
      "A symbol base_name is transformed without updating the base_name "
      "mapping")
    {
      symbolt &transformed_symbol = symbol_table.get_writeable_ref(symbol_name);
      // Transform the symbol
      transformed_symbol.base_name = "TransformTestBase";

      THEN("validate() should throw an exception")
      {
        REQUIRE_THROWS_AS(
          symbol_table.validate(validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
      // Reset symbol to a valid base_name after the previous test
      transformed_symbol.base_name = "TestBase";
    }
    WHEN(
      "A symbol module identifier is transformed without updating the module "
      "mapping")
    {
      symbolt &transformed_symbol = symbol_table.get_writeable_ref(symbol_name);
      transformed_symbol.module = "TransformTestModule";

      THEN("validate() should throw an exception")
      {
        REQUIRE_THROWS_AS(
          symbol_table.validate(validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
      // Reset symbol to a valid module name
      transformed_symbol.module = "TestModule";
    }
  }
}

SCENARIO("journalling_symbol_table_writer",
  "[core][utils][journalling_symbol_table_writer]")
{
  GIVEN("A journalling_symbol_table_writert wrapping an empty symbol_tablet")
  {
    symbol_tablet base_symbol_table;
    journalling_symbol_tablet symbol_table =
      journalling_symbol_tablet::wrap(base_symbol_table);
    const symbol_tablet &read_symbol_table=symbol_table;

    irep_idt symbol_name="Test";

    WHEN("A symbol is inserted into the symbol table")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      auto result=symbol_table.insert(symbol);
      THEN("The insert should succeed")
      {
        REQUIRE(result.second);
      }
      THEN("The inserted symbol should have the same name")
      {
        REQUIRE(result.first.name==symbol_name);
      }
      THEN(
        "The symbol table should return a symbol from a lookup of that name")
      {
        REQUIRE(read_symbol_table.lookup(symbol_name)!=nullptr);
      }
      THEN("The symbol table should return the same symbol from a lookup")
      {
        REQUIRE(&result.first==read_symbol_table.lookup(symbol_name));
      }
      THEN("The added symbol should appear in the updated collection")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==1);
      }
      THEN("The added symbol should not appear in the removed collection")
      {
        REQUIRE(symbol_table.get_removed().count(symbol_name)==0);
      }
      WHEN("Adding the same symbol again")
      {
        const auto result_re_insert = symbol_table.insert(symbol);
        THEN("The insert should fail")
        {
          REQUIRE(!result_re_insert.second);
        }
      }
    }
    WHEN("Moving a symbol into the symbol table")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      symbolt *symbol_in_table;
      auto result=symbol_table.move(symbol, symbol_in_table);
      THEN("The move should succeed")
      {
        REQUIRE(!result);
      }
      THEN(
        "The symbol table should return a symbol from a lookup of that name")
      {
        REQUIRE(read_symbol_table.lookup(symbol_name)!=nullptr);
      }
      THEN("The symbol table should return the same symbol from a lookup")
      {
        REQUIRE(symbol_in_table==read_symbol_table.lookup(symbol_name));
      }
      THEN("The added symbol should appear in the updated collection")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==1);
      }
      THEN("The added symbol should not appear in the removed collection")
      {
        REQUIRE(symbol_table.get_removed().count(symbol_name)==0);
      }
      WHEN("Moving the same symbol again")
      {
        symbolt *symbol_in_table2;
        const auto result_move = symbol_table.move(symbol, symbol_in_table2);
        THEN("The move should fail")
        {
          REQUIRE(result_move);
        }
        THEN("The returned pointer should match the previous move result")
        {
          REQUIRE(symbol_in_table==symbol_in_table2);
        }
      }
    }
    WHEN("Adding a symbol to the symbol table")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      auto result=symbol_table.add(symbol);
      THEN("The add should succeed")
      {
        REQUIRE(!result);
      }
      THEN(
        "The symbol table should return a symbol from a lookup of that name")
      {
        REQUIRE(read_symbol_table.lookup(symbol_name)!=nullptr);
      }
      THEN("The symbol table should return the same symbol from a lookup")
      {
        REQUIRE(symbol.name==read_symbol_table.lookup(symbol_name)->name);
      }
      THEN("The added symbol should appear in the updated collection")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==1);
      }
      THEN("The added symbol should not appear in the removed collection")
      {
        REQUIRE(symbol_table.get_removed().count(symbol_name)==0);
      }
      WHEN("Adding the same symbol again")
      {
        auto result_add_2 = symbol_table.add(symbol);
        THEN("The insert should fail")
        {
          REQUIRE(result_add_2);
        }
      }
    }
    WHEN("Updating an existing symbol")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      base_symbol_table.add(symbol);
      symbolt *writeable=symbol_table.get_writeable(symbol_name);

      THEN("get_writeable should succeed")
      {
        REQUIRE(writeable!=nullptr);
      }
      THEN("get_writeable should return the same pointer "
           "as the underlying table")
      {
        symbolt *writeable2=base_symbol_table.get_writeable(symbol_name);
        REQUIRE(writeable==writeable2);
      }
      THEN("get_writeable_ref should not throw")
      {
        symbol_table.get_writeable_ref(symbol_name);
      }
      THEN("The updated symbol should appear in the updated collection")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==1);
      }
      THEN("The updated symbol should not appear in the removed collection")
      {
        REQUIRE(symbol_table.get_removed().count(symbol_name)==0);
      }
    }
    WHEN("Removing a non-existent symbol")
    {
      irep_idt no_such_symbol_name = "DoesNotExist";
      bool ret = symbol_table.remove(no_such_symbol_name);
      THEN("The remove operation should fail")
      {
        REQUIRE(ret);
      }
      THEN("The symbol we failed to remove should appear in neither journal")
      {
        REQUIRE(symbol_table.get_updated().count(no_such_symbol_name) == 0);
        REQUIRE(symbol_table.get_removed().count(no_such_symbol_name) == 0);
      }
    }
    WHEN("Removing an existing symbol added via the journalling writer")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      symbol_table.add(symbol);
      bool ret=symbol_table.remove(symbol_name);
      THEN("The remove operation should succeed")
      {
        REQUIRE(!ret);
      }
      THEN("The symbol should appear in neither journal")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==0);
        REQUIRE(symbol_table.get_removed().count(symbol_name)==0);
      }
    }
    WHEN("Removing an existing symbol added outside the journalling writer")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      base_symbol_table.add(symbol);
      bool ret=symbol_table.remove(symbol_name);
      THEN("The remove operation should succeed")
      {
        REQUIRE(!ret);
      }
      THEN("The symbol we removed should be journalled as removed "
           "but not updated")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==0);
        REQUIRE(symbol_table.get_removed().count(symbol_name)==1);
      }
    }
    WHEN("Removing an existing symbol using an iterator (added via writer)")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      symbol_table.add(symbol);
      auto erase_iterator=read_symbol_table.symbols.find(symbol_name);
      symbol_table.erase(erase_iterator);
      THEN("The symbol should appear in neither journal")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==0);
        REQUIRE(symbol_table.get_removed().count(symbol_name)==0);
      }
    }
    WHEN("Removing an existing symbol using an iterator (added via base)")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      base_symbol_table.add(symbol);
      auto erase_iterator=read_symbol_table.symbols.find(symbol_name);
      symbol_table.erase(erase_iterator);
      THEN("The symbol should be journalled as removed")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==0);
        REQUIRE(symbol_table.get_removed().count(symbol_name)==1);
      }
    }
    WHEN("Re-adding a symbol previously removed")
    {
      symbolt symbol;
      symbol.name = symbol_name;
      const auto result_add_1 = symbol_table.add(symbol);
      symbol_table.remove(symbol.name);
      const auto result_add_2 = symbol_table.add(symbol);
      THEN("The first add should succeed")
      {
        REQUIRE(!result_add_1);
      }
      THEN("The second add should succeed")
      {
        REQUIRE(!result_add_2);
      }
      THEN("The symbol should be journalled as updated but not removed")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name)==1);
        REQUIRE(symbol_table.get_removed().count(symbol_name)==0);
      }
    }
  }
}
