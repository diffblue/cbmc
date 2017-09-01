/*******************************************************************\

Module: Unit tests for overlay_unordered_map

Author: Diffblue Ltd.

\*******************************************************************/

#include "catch.hpp"
#include <string>
#include <util/overlay_map.h>

TEST_CASE("Create and get a value from a overlay unordered map")
{
  overlay_unordered_mapt<std::string, std::string> map;
  map.set("foo", "bar");
  REQUIRE(map.at("foo")=="bar");
}

TEST_CASE("Move a value into unordered map, const at")
{
  overlay_unordered_mapt<std::string, std::string> map;
  std::string bar("bar");
  map.set("foo", std::move(bar));
  REQUIRE(map.at("foo")=="bar");
}

TEST_CASE(".at should throw out_of_range, if element doesn't exist")
{
  overlay_unordered_mapt<std::string, std::string> map;
  map.set("irn", "bru");
  REQUIRE_THROWS_AS(map.at("foo"), std::out_of_range);
}

TEST_CASE("Copy should have old elements")
{
  overlay_unordered_mapt<std::string, std::string> old;
  old.set("foo", "bar");
  auto copy=old.overlay();
  REQUIRE(copy.at("foo")=="bar");
}

TEST_CASE("Copy should not modify old elements")
{
  overlay_unordered_mapt<std::string, std::string> old;
  old.set("foo", "bar");
  auto copy=old.overlay();
  copy.set("foo", "something else");
  REQUIRE(old.at("foo")=="bar");
  REQUIRE(copy.at("foo")=="something else");
}

TEST_CASE("Changing old values should modify values in the copy")
{
  overlay_unordered_mapt<std::string, std::string> old;
  old.set("foo", "bar");
  auto copy=old.overlay();
  old.set("foo", "something else");
  REQUIRE(copy.at("foo")=="something else");
}

TEST_CASE("Construct from unordered_map")
{
  std::unordered_map<std::string, std::string> map;
  map.emplace("foo", "bar");
  overlay_unordered_mapt<std::string, std::string> overlay_map(std::move(map));
  REQUIRE(overlay_map.at("foo")=="bar");
  REQUIRE(map.empty());
}
