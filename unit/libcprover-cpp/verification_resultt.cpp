// Copyright (c) 2023 Fotis Koutoulakis for Diffblue Ltd.

/// \file Integration tests for the the interface of the class for verification
///       results produced by various verification engines (classes downstream
///       of goto_verifiert).

#include <libcprover-cpp/api.h>
#include <libcprover-cpp/verification_result.h>

#include <iostream>
#include <memory>
#include <sstream>
#include <string>

#include "../catch/catch.hpp"

SCENARIO(
  "When we analyse a model produced from some C code we get back verification "
  "results in a structured format",
  "[goto-checker][verification-result]")
{
  GIVEN("A model with a passing property from C source code")
  {
    api_sessiont api(api_optionst::buildert{}.build());
    api.load_model_from_files({"test2.c"});

    WHEN("We run that model past the verification engine")
    {
      const std::unique_ptr<verification_resultt> results = api.verify_model();

      THEN("The verification result should be success")
      {
        REQUIRE(results->final_result() == verifier_resultt::PASS);
      }

      THEN(
        "We should have access to the property and the property status should "
        "be PASS")
      {
        auto properties = results->get_property_ids();
        REQUIRE(properties.size() == 1);
        REQUIRE(properties.at(0) == "main.assertion.1");

        THEN(
          "The property description should be the same as the assertion "
          "description in the model")
        {
          const std::string assertion_description{
            "expected success: arr[3] to be 3"};
          const std::string results_description =
            results->get_property_description(properties.at(0));
          REQUIRE(assertion_description == results_description);
        }

        THEN("The property status should be PASS")
        {
          const auto property_status =
            results->get_property_status(properties.at(0));
          REQUIRE(property_status == prop_statust::PASS);
        }
      }
    }
  }

  GIVEN("A model with a failing property from C source code")
  {
    api_sessiont api(api_optionst::buildert{}.build());
    api.load_model_from_files({"test.c"});

    WHEN("We run that model past the verification engine")
    {
      const auto results = api.verify_model();

      THEN("The verification result should be failure")
      {
        REQUIRE(results->final_result() == verifier_resultt::FAIL);
      }
    }
  }
}
