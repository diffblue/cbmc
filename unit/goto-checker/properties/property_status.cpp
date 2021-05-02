// Copyright 2021 Michael Tautschnig

/// \file Tests operations on property_statust

#include <goto-checker/properties.h>

#include <testing-utils/use_catch.h>

TEST_CASE(
  "Preference order of properties",
  "[core][goto-checker][property_statust]")
{
  const property_statust error{property_statust::ERROR};
  const property_statust fail{property_statust::FAIL};
  const property_statust unknown{property_statust::UNKNOWN};
  const property_statust not_checked{property_statust::NOT_CHECKED};
  const property_statust not_reachable{property_statust::NOT_REACHABLE};
  const property_statust pass{property_statust::PASS};

  SECTION("Update a single property status")
  {
    property_statust status = property_statust::ERROR;
    status |= unknown;
    REQUIRE(status == property_statust::ERROR);
    status |= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::FAIL;
    status |= unknown;
    REQUIRE(status == property_statust::FAIL);
    status |= fail;
    REQUIRE(status == property_statust::FAIL);

    status = property_statust::UNKNOWN;
    status |= pass;
    REQUIRE(status == property_statust::PASS);
    status = property_statust::UNKNOWN;
    status |= not_reachable;
    REQUIRE(status == property_statust::NOT_REACHABLE);
    status = property_statust::UNKNOWN;
    status |= unknown;
    REQUIRE(status == property_statust::UNKNOWN);
    status = property_statust::UNKNOWN;
    status |= fail;
    REQUIRE(status == property_statust::FAIL);
    status = property_statust::UNKNOWN;
    status |= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::NOT_CHECKED;
    status |= pass;
    REQUIRE(status == property_statust::PASS);
    status = property_statust::NOT_CHECKED;
    status |= not_reachable;
    REQUIRE(status == property_statust::NOT_REACHABLE);
    status = property_statust::NOT_CHECKED;
    status |= not_checked;
    REQUIRE(status == property_statust::NOT_CHECKED);
    status = property_statust::NOT_CHECKED;
    status |= unknown;
    REQUIRE(status == property_statust::UNKNOWN);
    status = property_statust::NOT_CHECKED;
    status |= fail;
    REQUIRE(status == property_statust::FAIL);
    status = property_statust::NOT_CHECKED;
    status |= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::NOT_REACHABLE;
    status |= not_reachable;
    REQUIRE(status == property_statust::NOT_REACHABLE);
    status |= unknown;
    REQUIRE(status == property_statust::NOT_REACHABLE);

    status = property_statust::PASS;
    status |= pass;
    REQUIRE(status == property_statust::PASS);
    status |= unknown;
    REQUIRE(status == property_statust::PASS);
  }

  SECTION("Determine overall status")
  {
    property_statust status = property_statust::ERROR;
    status &= pass;
    REQUIRE(status == property_statust::ERROR);
    status &= not_reachable;
    REQUIRE(status == property_statust::ERROR);
    status &= not_checked;
    REQUIRE(status == property_statust::ERROR);
    status &= unknown;
    REQUIRE(status == property_statust::ERROR);
    status &= fail;
    REQUIRE(status == property_statust::ERROR);
    status &= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::FAIL;
    status &= pass;
    REQUIRE(status == property_statust::FAIL);
    status &= not_reachable;
    REQUIRE(status == property_statust::FAIL);
    status &= not_checked;
    REQUIRE(status == property_statust::FAIL);
    status &= unknown;
    REQUIRE(status == property_statust::FAIL);
    status &= fail;
    REQUIRE(status == property_statust::FAIL);
    status &= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::UNKNOWN;
    status &= pass;
    REQUIRE(status == property_statust::UNKNOWN);
    status &= not_reachable;
    REQUIRE(status == property_statust::UNKNOWN);
    status &= not_checked;
    REQUIRE(status == property_statust::UNKNOWN);
    status &= unknown;
    REQUIRE(status == property_statust::UNKNOWN);
    status &= fail;
    REQUIRE(status == property_statust::FAIL);
    status = property_statust::UNKNOWN;
    status &= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::NOT_CHECKED;
    status &= pass;
    REQUIRE(status == property_statust::NOT_CHECKED);
    status &= not_reachable;
    REQUIRE(status == property_statust::NOT_CHECKED);
    status &= not_checked;
    REQUIRE(status == property_statust::NOT_CHECKED);
    status &= unknown;
    REQUIRE(status == property_statust::UNKNOWN);
    status = property_statust::NOT_CHECKED;
    status &= fail;
    REQUIRE(status == property_statust::FAIL);
    status = property_statust::NOT_CHECKED;
    status &= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::NOT_REACHABLE;
    status &= pass;
    REQUIRE(status == property_statust::NOT_REACHABLE);
    status &= not_reachable;
    REQUIRE(status == property_statust::NOT_REACHABLE);
    status &= not_checked;
    REQUIRE(status == property_statust::NOT_CHECKED);
    status = property_statust::NOT_REACHABLE;
    status &= unknown;
    REQUIRE(status == property_statust::UNKNOWN);
    status = property_statust::NOT_REACHABLE;
    status &= fail;
    REQUIRE(status == property_statust::FAIL);
    status = property_statust::NOT_REACHABLE;
    status &= error;
    REQUIRE(status == property_statust::ERROR);

    status = property_statust::PASS;
    status &= pass;
    REQUIRE(status == property_statust::PASS);
    status &= not_reachable;
    REQUIRE(status == property_statust::NOT_REACHABLE);
    status = property_statust::PASS;
    status &= not_checked;
    REQUIRE(status == property_statust::NOT_CHECKED);
    status = property_statust::PASS;
    status &= unknown;
    REQUIRE(status == property_statust::UNKNOWN);
    status = property_statust::PASS;
    status &= fail;
    REQUIRE(status == property_statust::FAIL);
    status = property_statust::PASS;
    status &= error;
    REQUIRE(status == property_statust::ERROR);
  }
}
