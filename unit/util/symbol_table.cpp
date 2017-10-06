// Copyright 2016-2017 Diffblue Limited. All Rights Reserved.

/// \file Tests for symbol_tablet

#include <catch.hpp>
#include <util/recording_symbol_table.h>

SCENARIO("recording_symbol_table",
  "[core][utils][recording_symbol_table]")
{
  GIVEN("A recording_symbol_tablet wrapping an empty concrete_symbol_tablet")
  {
    concrete_symbol_tablet base_symbol_table;
    recording_symbol_tablet symbol_table=
      recording_symbol_tablet::wrap(base_symbol_table);
    WHEN("A symbol is copied into the symbol table")
    {
      irep_idt symbol_name1="Test1";
      symbolt symbol;
      symbol.name=symbol_name1;
      auto result=symbol_table.insert(symbol);
      THEN("The insert should succeed")
      {
        REQUIRE(result.second);
      }
      THEN("The inserted symbol should have the same name")
      {
        REQUIRE(result.first.name==symbol_name1);
      }
      THEN(
        "The symbol table should return a symbol from a lookup of that name")
      {
        REQUIRE(symbol_table.lookup(symbol_name1).has_value());
      }
      THEN("The symbol table should return the same symbol from a lookup")
      {
        REQUIRE(&result.first==&symbol_table.lookup(symbol_name1)->get());
      }
      THEN("The added symbol should appear in the updated collection")
      {
        REQUIRE(symbol_table.get_updated().count(symbol_name1)==1);
      }
      THEN("The added symbol should not appear in the removed collection")
      {
        REQUIRE(symbol_table.get_removed().count(symbol_name1)==0);
      }
      WHEN("Adding the same symbol again")
      {
        symbolt symbol;
        symbol.name=symbol_name1;
        auto result=symbol_table.insert(symbol);
        THEN("The insert should fail")
        {
          REQUIRE(!result.second);
        }
      }
      WHEN("Another symbol table is wrapped around the original symbol table")
      {
        recording_symbol_tablet symbol_table2=
          recording_symbol_tablet::wrap(symbol_table);
        WHEN("Adding the same symbol to the second symbol table")
        {
          symbolt symbol;
          symbol.name=symbol_name1;
          auto result=symbol_table.insert(symbol);
          THEN("The insert should fail")
          {
            REQUIRE(!result.second);
          }
        }
        WHEN("A symbol is moved into the new symbol table")
        {
          irep_idt symbol_name2="Test2";
          symbolt symbol;
          symbol.name=symbol_name2;
          auto result=symbol_table2.insert(std::move(symbol));
          THEN("The insert should succeed")
          {
            REQUIRE(result.second);
          }
          THEN("The inserted symbol should have the same name")
          {
            REQUIRE(result.first.name==symbol_name2);
          }
          THEN(
            "The original symbol table should return a symbol from a lookup "
              "of that name")
          {
            REQUIRE(symbol_table.lookup(symbol_name2).has_value());
          }
          THEN(
            "The new symbol table should return a symbol from a lookup "
              "of that name")
          {
            REQUIRE(symbol_table2.lookup(symbol_name2).has_value());
          }
          THEN(
            "The new symbol table should return the same symbol from a lookup")
          {
            REQUIRE(&result.first==&symbol_table2.lookup(symbol_name2)->get());
          }
          THEN(
            "The added symbol should appear in the updated collection of the "
              "original symbol table")
          {
            REQUIRE(symbol_table.get_updated().count(symbol_name2)==1);
          }
          THEN(
            "The added symbol should appear in the updated collection of the "
              "new symbol table")
          {
            REQUIRE(symbol_table2.get_updated().count(symbol_name2)==1);
          }
          THEN(
            "The added symbol should not appear in the removed collection of "
              "either symbol table")
          {
            REQUIRE(symbol_table.get_removed().count(symbol_name2)==0);
            REQUIRE(symbol_table2.get_removed().count(symbol_name2)==0);
          }
          WHEN("Using the original symbol name")
          {
            irep_idt symbol_name1="Test1";
            THEN(
              "Both symbol tables should return a symbol from a lookup "
                "of that name")
            {
              REQUIRE(symbol_table.lookup(symbol_name1).has_value());
              REQUIRE(symbol_table2.lookup(symbol_name1).has_value());
            }
            THEN(
              "The added symbol should appear in the updated collection "
                "of the original symbol table")
            {
              REQUIRE(symbol_table.get_updated().count(symbol_name1)==1);
            }
            THEN(
              "The added symbol should not appear in the updated collection "
                "of the new symbol table")
            {
              REQUIRE(symbol_table2.get_updated().count(symbol_name1)==0);
            }
            THEN(
              "The added symbol should not appear in the removed collection "
                "of either symbol table")
            {
              REQUIRE(symbol_table.get_removed().count(symbol_name1)==0);
              REQUIRE(symbol_table2.get_removed().count(symbol_name1)==0);
            }
          }
          WHEN("Removing the second symbol from the second map")
          {
            bool failure=symbol_table2.remove(symbol_name2);
            THEN("The remove should succeed")
            {
              REQUIRE(!failure);
            }
            THEN("The second symbol should not appear in either map")
            {
              REQUIRE(!symbol_table.lookup(symbol_name2).has_value());
              REQUIRE(!symbol_table2.lookup(symbol_name2).has_value());
            }
            THEN(
              "The second symbol should not appear in the updated "
                "collection of either symbol table")
            {
              REQUIRE(symbol_table.get_updated().count(symbol_name2)==0);
              REQUIRE(symbol_table2.get_updated().count(symbol_name2)==0);
            }
            THEN(
              "The second symbol should not appear in the removed "
                "collection of either symbol table")
            {
              REQUIRE(symbol_table.get_removed().count(symbol_name2)==0);
              REQUIRE(symbol_table2.get_removed().count(symbol_name2)==0);
            }
          }
          WHEN("Removing the first symbol from the second map")
          {
            bool failure=symbol_table2.remove(symbol_name1);
            THEN("The remove should succeed")
            {
              REQUIRE(!failure);
            }
            THEN("The first symbol should not appear in either map")
            {
              REQUIRE(!symbol_table.lookup(symbol_name1).has_value());
              REQUIRE(!symbol_table2.lookup(symbol_name1).has_value());
            }
            THEN(
              "The first symbol should not appear in the updated "
                "collection of either symbol table")
            {
              REQUIRE(symbol_table.get_updated().count(symbol_name1)==0);
              REQUIRE(symbol_table2.get_updated().count(symbol_name1)==0);
            }
            THEN(
              "The first symbol should not appear in the removed "
                "collection of the first symbol table")
            {
              REQUIRE(symbol_table.get_removed().count(symbol_name1)==0);
            }
            THEN(
              "The first symbol should appear in the removed "
                "collection of the second symbol table")
            {
              REQUIRE(symbol_table2.get_removed().count(symbol_name1)==1);
            }
            WHEN("Removing the first symbol from the second map again")
            {
              bool failure=symbol_table2.remove(symbol_name1);
              THEN("The remove should fail")
              {
                REQUIRE(failure);
              }
            }
            WHEN("Adding the first symbol back into the second map")
            {
              symbolt symbol;
              symbol.name=symbol_name1;
              auto result=symbol_table.insert(symbol);
              THEN("The insert should succeed")
              {
                REQUIRE(result.second);
              }
              THEN(
                "Both symbol tables should return a symbol from a lookup "
                  "of that name")
              {
                REQUIRE(symbol_table.lookup(symbol_name1).has_value());
                REQUIRE(symbol_table2.lookup(symbol_name1).has_value());
              }
              THEN(
                "Both symbol tables should return the same symbol from a "
                  "lookup")
              {
                REQUIRE(
                  &result.first==&symbol_table.lookup(symbol_name1)->get());
                REQUIRE(
                  &result.first==&symbol_table2.lookup(symbol_name1)->get());
              }
              THEN(
                "The added symbol should appear in the updated collection of "
                  "both symbol tables")
              {
                REQUIRE(symbol_table.get_updated().count(symbol_name2)==1);
                REQUIRE(symbol_table2.get_updated().count(symbol_name2)==1);
              }
              THEN(
                "The added symbol should not appear in the removed collection "
                  "of either symbol table")
              {
                REQUIRE(symbol_table.get_removed().count(symbol_name2)==0);
                REQUIRE(symbol_table2.get_removed().count(symbol_name2)==0);
              }
              WHEN("Removing the first symbol from the second map again")
              {
                bool failure=symbol_table2.remove(symbol_name1);
                THEN("The remove should succeed")
                {
                  REQUIRE(!failure);
                }
                THEN("The first symbol should not appear in either map")
                {
                  REQUIRE(!symbol_table.lookup(symbol_name1).has_value());
                  REQUIRE(!symbol_table2.lookup(symbol_name1).has_value());
                }
                THEN(
                  "The first symbol should not appear in the updated "
                    "collection of either symbol table")
                {
                  REQUIRE(symbol_table.get_updated().count(symbol_name1)==0);
                  REQUIRE(symbol_table2.get_updated().count(symbol_name1)==0);
                }
                THEN(
                  "The first symbol should not appear in the removed "
                    "collection of the first symbol table")
                {
                  REQUIRE(symbol_table.get_removed().count(symbol_name1)==0);
                }
                THEN(
                  "The first symbol should appear in the removed "
                    "collection of the second symbol table")
                {
                  REQUIRE(symbol_table2.get_removed().count(symbol_name1)==1);
                }
              }
            }
          }
          // This is equivalent to removing a symbol after the second symbol
          // table is finished with - its updated/removed should be unaffected
          WHEN("Removing the second symbol from the first map")
          {
            bool failure=symbol_table.remove(symbol_name2);
            THEN("The remove should succeed")
            {
              REQUIRE(!failure);
            }
            THEN("The second symbol should not appear in either map")
            {
              REQUIRE(!symbol_table.lookup(symbol_name2).has_value());
              REQUIRE(!symbol_table2.lookup(symbol_name2).has_value());
            }
            THEN(
              "The second symbol should not appear in the updated "
                "collection of the first symbol table")
            {
              REQUIRE(symbol_table.get_updated().count(symbol_name2)==0);
            }
            THEN(
              "The second symbol should appear in the updated "
                "collection of the second symbol table")
            {
              REQUIRE(symbol_table2.get_updated().count(symbol_name2)==1);
            }
            THEN(
              "The second symbol should not appear in the removed "
                "collection of either symbol table")
            {
              REQUIRE(symbol_table.get_removed().count(symbol_name2)==0);
              REQUIRE(symbol_table2.get_removed().count(symbol_name2)==0);
            }
          }
        }
      }
    }
  }
}
