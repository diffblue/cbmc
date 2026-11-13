/*******************************************************************\

Module: Unit tests for loop hash computation

Author: CBMC Team

\*******************************************************************/

#include <goto-programs/goto_function.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/loop_ids.h>

#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "Loop hash computation produces stable identifiers",
  "[core][goto-programs][loop-hash]")
{
  GIVEN("A program with two loops")
  {
    const std::string code = R"(
      int main() {
        int sum = 0;
        
        // Loop 1: Simple for loop
        for(int i = 0; i < 10; i++) {
          sum += i;
        }
        
        // Loop 2: While loop
        int j = 0;
        while(j < 5) {
          sum += j * 2;
          j++;
        }
        
        return sum;
      }
    )";

    auto goto_model = get_goto_model_from_c(code);

    WHEN("Loop hashes are computed")
    {
      goto_model.goto_functions.update();
      goto_model.goto_functions.compute_loop_hashes();

      THEN("Each backwards goto has a non-zero hash")
      {
        const auto &main_func =
          goto_model.goto_functions.function_map.at("main");

        int loop_count = 0;
        for(const auto &inst : main_func.body.instructions)
        {
          if(inst.is_backwards_goto())
          {
            loop_count++;
            REQUIRE(inst.loop_hash != 0);
          }
        }

        REQUIRE(loop_count > 0);
      }
    }
  }

  GIVEN("A program with nested loops")
  {
    const std::string code = R"(
      int main() {
        int sum = 0;
        
        for(int i = 0; i < 3; i++) {
          for(int j = 0; j < 3; j++) {
            sum += i * j;
          }
        }
        
        return sum;
      }
    )";

    auto goto_model = get_goto_model_from_c(code);

    WHEN("Loop hashes are computed")
    {
      goto_model.goto_functions.update();
      goto_model.goto_functions.compute_loop_hashes();

      THEN("Inner and outer loops have different hashes")
      {
        const auto &main_func =
          goto_model.goto_functions.function_map.at("main");

        std::vector<std::size_t> hashes;
        for(const auto &inst : main_func.body.instructions)
        {
          if(inst.is_backwards_goto())
          {
            hashes.push_back(inst.loop_hash);
          }
        }

        REQUIRE(hashes.size() == 2);
        REQUIRE(hashes[0] != hashes[1]);
        REQUIRE(hashes[0] != 0);
        REQUIRE(hashes[1] != 0);
      }
    }
  }
}

SCENARIO(
  "Loop hashes are deterministic across compilations",
  "[core][goto-programs][loop-hash]")
{
  GIVEN("A program with two loops compiled twice")
  {
    const std::string code = R"(
      int main() {
        int sum = 0;

        for(int i = 0; i < 10; i++) {
          sum += i;
        }

        int j = 0;
        while(j < 5) {
          sum += j * 2;
          j++;
        }

        return sum;
      }
    )";

    auto model1 = get_goto_model_from_c(code);
    model1.goto_functions.update();
    model1.goto_functions.compute_loop_hashes();

    auto model2 = get_goto_model_from_c(code);
    model2.goto_functions.update();
    model2.goto_functions.compute_loop_hashes();

    WHEN("Hashes are compared")
    {
      const auto &main1 = model1.goto_functions.function_map.at("main");
      const auto &main2 = model2.goto_functions.function_map.at("main");

      std::vector<std::size_t> hashes1, hashes2;
      for(const auto &inst : main1.body.instructions)
      {
        if(inst.is_backwards_goto())
          hashes1.push_back(inst.loop_hash);
      }
      for(const auto &inst : main2.body.instructions)
      {
        if(inst.is_backwards_goto())
          hashes2.push_back(inst.loop_hash);
      }

      THEN("Both compilations produce identical hashes")
      {
        REQUIRE(hashes1.size() == hashes2.size());
        REQUIRE(hashes1 == hashes2);
        for(auto h : hashes1)
          REQUIRE(h != 0);
      }
    }
  }
}

SCENARIO(
  "Loop hashes remain stable when do-while-0 pseudo-loops are added",
  "[core][goto-programs][loop-hash]")
{
  GIVEN("A program with two loops")
  {
    const std::string original_code = R"(
      int main() {
        int sum = 0;
        for(int i = 0; i < 10; i++) {
          sum += i;
        }
        int j = 0;
        while(j < 5) {
          sum += j * 2;
          j++;
        }
        return sum;
      }
    )";

    auto original_model = get_goto_model_from_c(original_code);
    original_model.goto_functions.update();
    original_model.goto_functions.compute_loop_hashes();

    const auto &original_main =
      original_model.goto_functions.function_map.at("main");

    std::vector<std::size_t> original_hashes;
    for(const auto &inst : original_main.body.instructions)
    {
      if(inst.is_backwards_goto())
        original_hashes.push_back(inst.loop_hash);
    }

    REQUIRE(original_hashes.size() == 2);

    WHEN("do-while-0 pseudo-loops are added before the real loops")
    {
      const std::string modified_code = R"(
        int main() {
          int sum = 0;
          do { sum += 1; } while(0);
          do { sum += 2; } while(0);
          do { sum += 3; } while(0);
          for(int i = 0; i < 10; i++) {
            sum += i;
          }
          int j = 0;
          while(j < 5) {
            sum += j * 2;
            j++;
          }
          return sum;
        }
      )";

      auto modified_model = get_goto_model_from_c(modified_code);
      modified_model.goto_functions.update();
      modified_model.goto_functions.compute_loop_hashes();

      const auto &modified_main =
        modified_model.goto_functions.function_map.at("main");

      std::vector<std::size_t> modified_hashes;
      for(const auto &inst : modified_main.body.instructions)
      {
        if(inst.is_backwards_goto())
          modified_hashes.push_back(inst.loop_hash);
      }

      THEN("The original loops maintain their hash values")
      {
        REQUIRE(modified_hashes.size() == 5);

        bool found_for = false;
        bool found_while = false;
        for(std::size_t hash : modified_hashes)
        {
          if(hash == original_hashes[0])
            found_for = true;
          if(hash == original_hashes[1])
            found_while = true;
        }

        REQUIRE(found_for);
        REQUIRE(found_while);
      }
    }
  }
}

SCENARIO(
  "Loop hash computation for different loop structures",
  "[core][goto-programs][loop-hash]")
{
  GIVEN("Different types of loops")
  {
    WHEN("Testing a for loop")
    {
      const std::string code = R"(
        int main() {
          int sum = 0;
          for(int i = 0; i < 10; i++) {
            sum += i;
          }
          return sum;
        }
      )";

      auto goto_model = get_goto_model_from_c(code);
      goto_model.goto_functions.update();
      goto_model.goto_functions.compute_loop_hashes();

      THEN("The loop has a valid hash")
      {
        const auto &main_func =
          goto_model.goto_functions.function_map.at("main");

        bool found_loop = false;
        for(const auto &inst : main_func.body.instructions)
        {
          if(inst.is_backwards_goto())
          {
            found_loop = true;
            REQUIRE(inst.loop_hash != 0);
          }
        }
        REQUIRE(found_loop);
      }
    }

    WHEN("Testing a while loop")
    {
      const std::string code = R"(
        int main() {
          int sum = 0;
          int i = 0;
          while(i < 10) {
            sum += i;
            i++;
          }
          return sum;
        }
      )";

      auto goto_model = get_goto_model_from_c(code);
      goto_model.goto_functions.update();
      goto_model.goto_functions.compute_loop_hashes();

      THEN("The loop has a valid hash")
      {
        const auto &main_func =
          goto_model.goto_functions.function_map.at("main");

        bool found_loop = false;
        for(const auto &inst : main_func.body.instructions)
        {
          if(inst.is_backwards_goto())
          {
            found_loop = true;
            REQUIRE(inst.loop_hash != 0);
          }
        }
        REQUIRE(found_loop);
      }
    }

    WHEN("Testing a do-while loop")
    {
      const std::string code = R"(
        int main() {
          int sum = 0;
          int i = 0;
          do {
            sum += i;
            i++;
          } while(i < 10);
          return sum;
        }
      )";

      auto goto_model = get_goto_model_from_c(code);
      goto_model.goto_functions.update();
      goto_model.goto_functions.compute_loop_hashes();

      THEN("The loop has a valid hash")
      {
        const auto &main_func =
          goto_model.goto_functions.function_map.at("main");

        bool found_loop = false;
        for(const auto &inst : main_func.body.instructions)
        {
          if(inst.is_backwards_goto())
          {
            found_loop = true;
            REQUIRE(inst.loop_hash != 0);
          }
        }
        REQUIRE(found_loop);
      }
    }
  }
}

SCENARIO(
  "Loop hash stability with body changes",
  "[core][goto-programs][loop-hash]")
{
  GIVEN("A loop with a specific structure")
  {
    const std::string original_code = R"(
      int main() {
        int sum = 0;
        for(int i = 0; i < 10; i++) {
          sum += i;
        }
        return sum;
      }
    )";

    auto original_model = get_goto_model_from_c(original_code);
    original_model.goto_functions.update();
    original_model.goto_functions.compute_loop_hashes();

    const auto &original_main =
      original_model.goto_functions.function_map.at("main");

    std::size_t original_hash = 0;
    for(const auto &inst : original_main.body.instructions)
    {
      if(inst.is_backwards_goto())
      {
        original_hash = inst.loop_hash;
        break;
      }
    }
    REQUIRE(original_hash != 0);

    WHEN("The loop body changes")
    {
      const std::string modified_code = R"(
        int main() {
          int sum = 0;
          for(int i = 0; i < 10; i++) {
            sum += i * 2;  // Changed operation
          }
          return sum;
        }
      )";

      auto modified_model = get_goto_model_from_c(modified_code);
      modified_model.goto_functions.update();
      modified_model.goto_functions.compute_loop_hashes();

      const auto &modified_main =
        modified_model.goto_functions.function_map.at("main");

      std::size_t modified_hash = 0;
      for(const auto &inst : modified_main.body.instructions)
      {
        if(inst.is_backwards_goto())
        {
          modified_hash = inst.loop_hash;
          break;
        }
      }
      REQUIRE(modified_hash != 0);

      THEN("The hash changes because the loop structure changed")
      {
        // When the loop body changes, the hash should also change
        // This test verifies that the hash is sensitive to structural changes
        REQUIRE(modified_hash != original_hash);
      }
    }
  }
}
