#include "parsing.h"
#include "basic.h"
#include <gtest/gtest.h>
#include <fstream>

void test_parse(const char *s, const Term &t)
{
   try
   {
      Term result = parse(s);
      EXPECT_EQ(result, t);
   }
   catch (std::runtime_error &e)
   {
      ASSERT_TRUE(false) << "Parsing '" << s
         << "' an exception was thrown but this was not expected: "
         << e.what();
   }
}

void test_parse_exception(const char *s)
{
   EXPECT_ANY_THROW(parse(s)) << "parsing " << s;
}

void check_exception_text(
        std::function<void()> f, const std::string &expected_text)
{
    try
    {
        f();
    }
    catch (std::runtime_error &e)
    {
        EXPECT_EQ(e.what(), expected_text);
    }
}

void test_parse_environment(const char *input, const char *check_name, Term t)
{
   Environment e;
   std::stringbuf buf(input);
   parse_environment(buf, e, { "" });
   EXPECT_EQ(e.type_of(check_name), t) << "input: " << input;
}

void test_parse_environment_exception(const char *input)
{
   Environment e;
   std::stringbuf buf(input);
   EXPECT_ANY_THROW(parse_environment(buf, e, { "" })) << "input: " << input;
}

TEST(Parsing, Identifier)
{
   test_parse("a", Identifier("a"));
   test_parse_exception("#");
   test_parse_exception("%");
   test_parse("q", Identifier("q"));
   test_parse("\tq", Identifier("q"));
   test_parse("q\r\n", Identifier("q"));
   test_parse("X", Identifier("X"));
   test_parse("H", Identifier("H"));
   test_parse("_c", Identifier("_c"));
   test_parse("a'", Identifier("a'"));
   test_parse("a3", Identifier("a3"));
   test_parse("a9", Identifier("a9"));
   test_parse_exception("3a");
   test_parse_exception("7a");
   test_parse(" a9", Identifier("a9"));
   test_parse("  a9", Identifier("a9"));
   test_parse("(mod.v)", Identifier("mod", "v"));
   test_parse("Prop", Prop());
   test_parse("Type", Type());
   test_parse("Type3a", Identifier("Type3a"));
   test_parse_exception("Type3 %");
   test_parse("forall4", Identifier("forall4"));
   test_parse_exception("Prop%");
   test_parse("Prop ", Prop());
}

TEST(Parsing, BindVariable)
{
   test_parse("forall P: Prop, Prop", Forall("P", Prop(), Prop()));
   test_parse("forall Q: Prop, Prop", Forall("Q", Prop(), Prop()));
   test_parse_exception("forall");
   test_parse_exception("forall Q; Prop, Prop");
   test_parse("forall Q : Prop, Prop", Forall("Q", Prop(), Prop()));
   test_parse("forall P: Type, Prop", Forall("P", Type(), Prop()));
   test_parse_exception("forall P: Prop. Prop");
   test_parse("forall P: Prop , Prop", Forall("P", Prop(), Prop()));
   test_parse("forall P: Prop, A", Forall("P", Prop(), Identifier("A")));
   test_parse("forall P: Prop, A ", Forall("P", Prop(), Identifier("A")));
   test_parse("lambda P: Prop, Prop", Lambda("P", Prop(), Prop()));
}

TEST(Parsing, Apply)
{
   test_parse("forall P: A B, Prop",
      Forall("P", Apply(Identifier("A"), Identifier("B")), Prop()));
   test_parse("forall P: A B C, Prop",
      Forall("P",
         Apply(Apply(Identifier("A"), Identifier("B")), Identifier("C")),
         Prop()));
   test_parse("forall P: Prop, A B",
      Forall("P", Prop(), Apply(Identifier("A"), Identifier("B"))));
   test_parse("A B", Apply(Identifier("A"), Identifier("B")));
}

TEST(Parsing, Parentheses)
{
   test_parse("(A)", Identifier("A"));
   test_parse("(A) ", Identifier("A"));
   test_parse("( A) ", Identifier("A"));
}

TEST(Parsing, Axiom)
{
   test_parse_environment("Axiom P: Prop.", "P", Prop());
   test_parse_environment_exception("Axiam P: Prop.");
   test_parse_environment("Axiom Q: Prop.", "Q", Prop());
   test_parse_environment_exception("Axiom P; Prop.");
   test_parse_environment("Axiom P: Type.", "P", Type());
   test_parse_environment_exception("Axiom P: Prop,");
   test_parse_environment("Axiom P: Prop. Axiom Q: Prop.", "Q", Prop());
}

TEST(Parsing, Definition)
{
   test_parse_environment("Definition P: Type := Prop.", "P", Type());
   test_parse_environment("Definition Q: Type := Prop.", "Q", Type());
   test_parse_environment("Definition P: Type := Type.", "P", Type());
}

TEST(Parsing, Underscore)
{
   test_parse_environment_exception("Axiom P: forall _: Prop, _.");
   test_parse_environment_exception("Axiom _: forall P: Prop, P.");
   test_parse_environment_exception("Definition _: Prop := forall P: Prop, P.");
}

TEST(Parsing, Arrow)
{
   test_parse_environment("Axiom f: Prop -> Prop.", "f",
      Forall("_", Prop(), Prop()));
   test_parse_environment("Axiom f: Type -> Type.", "f",
      Forall("_", Type(), Type()));
   test_parse_environment_exception("Axiom f: Prop - > Prop.");
   test_parse_environment("Axiom f: (Prop -> Prop) -> Prop.", "f",
      Forall("_", Forall("_", Prop(), Prop()), Prop()));
   test_parse_environment("Axiom f: Prop -> Prop -> Prop.", "f",
      Forall("_", Prop(), Forall("_", Prop(), Prop())));
   test_parse_environment("Axiom f: Prop -> forall P: Prop, P.", "f",
      Forall("_", Prop(), Forall("P", Prop(), Identifier("P"))));
   test_parse_environment(
      "Axiom P: forall P: Prop, P -> P.",
      "P",
      Forall("P", Prop(), Forall("_", Identifier("P"), Identifier("P"))));
   test_parse("P t -> P u",
      Forall("_", Apply(Identifier("P"), Identifier("t")),
                  Apply(Identifier("P"), Identifier("u"))));
}

TEST(Parsing, Comment)
{
   test_parse_environment("Axiom #comment\n P: Prop.", "P", Prop());
   test_parse_environment("Axiom #comment\r P: Prop.", "P", Prop());
   test_parse_environment("Axiom P: Prop. #comment", "P", Prop());
   test_parse_environment("Axiom P:#comment\n Prop.", "P", Prop());
   test_parse_environment("Axiom P:#cm\n#cm\n Prop.", "P", Prop());
}

TEST(Parsing, ForallDoesNotDependOnVariable)
{
   Environment e;
   std::stringbuf buf(
      "Definition true_is_true: forall P: Prop, P -> P "
      ":= lambda P: Prop, lambda p: P, p.");
   parse_environment(buf, e, { "" });
}

TEST(Parsing, Equal)
{
   Environment e;
   std::stringbuf buf(
      "Definition equal: forall S: Type, S -> S -> Prop"
      ":= lambda S: Type,"
      "   lambda s1: S,"
      "   lambda s2: S,"
      "   forall P: S -> Prop,"
      "   P s1 ->"
      "   P s2.");
   parse_environment(buf, e, { "" });
}

TEST(Parsing, RequireFromTest)
{
   Environment e;
   std::stringbuf buf("Require test1.");
   parse_environment(buf, e, { "test" });
   e.type_of("Thing");
   e.type_of(Name("test1", "Thing"));
}

TEST(Parsing, RequireNonExistent)
{
   Environment e;
   std::stringbuf buf("Require does_not_exist.");
   EXPECT_ANY_THROW(parse_environment(buf, e, { "test" }));
}

TEST(Parsing, ModulesDisambiguate)
{
   Environment e;
   std::stringbuf buf("Require test1. Require test2.");
   parse_environment(buf, e, { "test" });
   EXPECT_EQ(e.type_of(Name("test1", "Thing")), Prop());
   EXPECT_EQ(e.type_of(Name("test2", "Thing")), Type());
   EXPECT_EQ(e.type_of(Name("test1", "Thang")), Prop());
   EXPECT_EQ(e.type_of(Name("test2", "Thang")), Type());
}

// test3 uses 'Thing' which is defined in test1 but it does not Require test1.
// Because of this an exception is thrown.
TEST(Parsing, NeedToImport)
{
   check_exception_text(
      []()
      {
         Environment e;
         std::stringbuf buf("Require test1. Require test3.");
         parse_environment(buf, e, { "test" });
      },
      "test3.s:2: Identifier Thing was not declared");
}

TEST(Parsing, EmptyLines)
{
   check_exception_text(
      []()
      {
         Environment e;
         std::stringbuf buf("Axiom p: Prop.\nAxiom q: Prop.\n\nAxiom n: bla.");
         parse_environment(buf, e, { "test" });
      },
      "test:4: Identifier bla was not declared");
}

TEST(Parsing, StandardEnvironment)
{
   Environment e;
   std::stringbuf buf(
        "Require plus. Require logic. Require mult.");
   parse_environment(buf, e, { "lib" });
   e.type_of("True");
}

TEST(Parsing, IndirectLibraryImport)
{
    Environment e;
    std::stringbuf buf("Require test4.");
    parse_environment(buf, e, { "test", "lib" });
    e.type_of(Name("logic", "True"));
}

