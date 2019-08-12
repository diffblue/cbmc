#include <memory>
#include <testing-utils/use_catch.h>
#include <util/make_unique.h>
#include <util/type_identifier.h>

TEST_CASE("can use fake_dynamic_cast to cast to bottom class", "[core][util]")
{
  class Top : public has_type_indext
  {
  };

  class BottomA final : public Top
  {
  public:
    const void *
    match_type_identifier(const type_identifiert &identifier) const override
    {
      if(identifier == type_identifiert::get<BottomA>())
      {
        return this;
      }
      else
      {
        return nullptr;
      }
    }
  };

  class BottomB final : public Top
  {
  public:
    const void *
    match_type_identifier(const type_identifiert &identifier) const override
    {
      if(identifier == type_identifiert::get<BottomB>())
      {
        return this;
      }
      else
      {
        return nullptr;
      }
    }
  };

  std::unique_ptr<Top> bottom_a = util_make_unique<BottomA>();
  std::unique_ptr<Top> bottom_b = util_make_unique<BottomB>();

  REQUIRE(fake_dynamic_cast<BottomA *>(bottom_a.get()) != nullptr);
  REQUIRE(fake_dynamic_cast<const BottomA *>(bottom_a.get()) != nullptr);
  const Top *c_bottom_a = bottom_a.get();
  REQUIRE(fake_dynamic_cast<const BottomA *>(c_bottom_a) != nullptr);
  REQUIRE(fake_dynamic_cast<BottomB *>(bottom_a.get()) == nullptr);

  REQUIRE(fake_dynamic_cast<BottomA *>(bottom_b.get()) == nullptr);
  REQUIRE(fake_dynamic_cast<const BottomB *>(bottom_b.get()) != nullptr);
  const Top *c_bottom_b = bottom_b.get();
  REQUIRE(fake_dynamic_cast<const BottomB *>(c_bottom_b) != nullptr);
  REQUIRE(fake_dynamic_cast<BottomB *>(bottom_b.get()) != nullptr);
}

TEST_CASE(
  "fake_dynamic cast can cast through a linear hierarchy",
  "[core][util]")
{
  class Top : public has_type_indext
  {
  };

  class Middle : public Top
  {
  public:
    const void *
    match_type_identifier(const type_identifiert &identifier) const override
    {
      if(identifier == type_identifiert::get<Middle>())
      {
        return this;
      }
      else
      {
        return nullptr;
      }
    }
  };

  class Bottom : public Middle
  {
    const void *
    match_type_identifier(const type_identifiert &identifier) const override
    {
      if(identifier == type_identifiert::get<Bottom>())
      {
        return this;
      }
      return Middle::match_type_identifier(identifier);
    }
  };

  Bottom bottom;
  Top *pBottom = &bottom;
  REQUIRE(fake_dynamic_cast<Bottom *>(pBottom) != nullptr);
  REQUIRE(fake_dynamic_cast<Middle *>(pBottom) != nullptr);
}

TEST_CASE(
  "fake_dynamic_cast can cast through diamond inheritance",
  "[core][util]")
{
  struct Top : public virtual has_type_indext
  {
  };
  struct Left : public virtual Top
  {
    const void *
    match_type_identifier(const type_identifiert &identifier) const override
    {
      if(identifier == type_identifiert::get<Left>())
      {
        return this;
      }
      return nullptr;
    }
  };
  struct Right : public virtual Top
  {
    const void *
    match_type_identifier(const type_identifiert &identifiert) const override
    {
      if(identifiert == type_identifiert::get<Right>())
      {
        return this;
      }
      return nullptr;
    }
  };
  struct Bottom : public Left, public Right
  {
  private:
    const void *
    match_type_identifier(const type_identifiert &identifier) const override
    {
      if(identifier == type_identifiert::get<Bottom>())
      {
        return this;
      }
      auto left = Left::match_type_identifier(identifier);
      if(left != nullptr)
      {
        return left;
      }
      return Right::match_type_identifier(identifier);
    }
  };

  Bottom bottom;
  Top *pBottom = &bottom;
  REQUIRE(fake_dynamic_cast<Bottom *>(pBottom) != nullptr);
  REQUIRE(fake_dynamic_cast<Left *>(pBottom) != nullptr);
  REQUIRE(fake_dynamic_cast<Right *>(pBottom) != nullptr);
}
