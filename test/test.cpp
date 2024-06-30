#include "system.h"
#include "basic.h"
#include <gtest/gtest.h>

void expect_eq(const std::string & msg, const Term &t1, const Term &t2)
{
   EXPECT_EQ(t1, t2) << msg;
}

void expect_ne(const Term &t1, const Term &t2)
{
   EXPECT_NE(t1, t2);
}

TEST(Module, Identifier)
{
   Term t(Identifier("module", "var"));
   std::ostringstream os;
   os << t;
   EXPECT_EQ(os.str(), "module.var");
}

TEST(Print, TypeSucc)
{
   std::ostringstream os;
   os << Term(TypeSucc(Type()));
   EXPECT_EQ(os.str(), "TypeSucc(Type)");
}

TEST(Print, TypeMax)
{
   std::ostringstream os;
   os << Term(TypeMax(Type(), Prop()));
   EXPECT_EQ(os.str(), "TypeMax(Type, Prop)");
}

TEST(Types, Equality)
{
   expect_eq("eq-1", Prop(), Prop());
   expect_ne(Prop(), Type());
   expect_eq("eq-t", Type(), Type());
   expect_eq("eq-2", Identifier("x"), Identifier("x"));
   expect_ne(Identifier("x"), Identifier("mod", "x"));
   expect_ne(Identifier("mod", "x"), Identifier("mod", "y"));
   expect_ne(Forall("x", Prop(), Identifier("x")),
             Forall("y", Prop(), Identifier("x")));
   expect_ne(Forall("x", Prop(), Identifier("x")),
             Forall("x", Type(), Identifier("x")));
   expect_ne(Forall("x", Prop(), Identifier("x")),
             Forall("x", Prop(), Identifier("y")));
   expect_eq("eq-3",
             Forall("x", Prop(), Identifier("x")),
             Forall("y", Prop(), Identifier("y")));
   expect_ne(Forall("x", Prop(), Identifier("x")),
             Forall("y", Type(), Identifier("y")));
}

TEST(Types, TypeOf)
{
   Environment e;
   expect_eq("eq-1", type_of(e, Prop()), TypeSucc(Prop()));
   expect_eq("eq-2", type_of(e, Type()), TypeSucc(Type()));
}

void TestFreeVariables(const Term &t, const VariableVector &v)
{
   EXPECT_EQ(free_variables(t), v) << "free variables of " << t;
}

TEST(FreeVariables, FreeVariables)
{
   TestFreeVariables(Identifier("x"), { "x" });
   TestFreeVariables(Identifier("mod", "x"), {});
   TestFreeVariables(Prop(), {});
   TestFreeVariables(Forall("x", Identifier("y"), Identifier("x")), { "y" });
   TestFreeVariables(Forall("x", Identifier("y"), Identifier("z")),
                     { "y", "z" });
   TestFreeVariables(Forall("x", Identifier("x"), Identifier("x")), { "x" });
   TestFreeVariables(Forall("x", Identifier("y"), Identifier("y")), { "y" });
   TestFreeVariables(Lambda("x", Identifier("y"), Identifier("x")), { "y" });
   TestFreeVariables(Lambda("x", Identifier("y"), Identifier("z")),
                     { "y", "z" });
   TestFreeVariables(Apply(Identifier("y"), Identifier("x")),
                     { "x", "y" });
}

TEST(NewVariable, NewVariable)
{
   ASSERT_EQ(new_variable("x", {}), "x");
   ASSERT_EQ(new_variable("x", { { "x" } }), "x0");
   ASSERT_EQ(new_variable("x", { { "x" } , { "x0" } }), "x1");
   ASSERT_EQ(new_variable("x", { { "x" } , { "x0" }, { "y1" } }), "x1");
   ASSERT_EQ(new_variable("x2", { { "x2" } , { "x3" } , { "x4" } }), "x5");
   ASSERT_EQ(new_variable("var2", { { "var2" } }), "var3");
   ASSERT_EQ(new_variable("x11", { { "x11" }, { "x12" }}), "x13");
}

TEST(Environment, Axiom)
{
   Environment e;
   e.axiom("P", Prop());
   e.axiom("Q", Type());
   ASSERT_ANY_THROW(e.axiom("P", Prop()));
   expect_eq("eq-1", type_of(e, Identifier("P")), Prop());
   expect_eq("eq-2", type_of(e, Identifier("Q")), Type());
   ASSERT_ANY_THROW(type_of(e, Identifier("R")));
}

TEST(Environment, TypeOfAxiom)
{
   Environment e;
   e.axiom("P", Prop());
   e.axiom("p", Identifier("P"));
   ASSERT_ANY_THROW(e.axiom("q", Identifier("p")));
   ASSERT_ANY_THROW(e.type_of("q"));
}

TEST(Environment, Definition)
{
   Environment e;
   e.axiom("P", Prop());
   e.definition("Q", Prop(), Identifier("P"));
   ASSERT_ANY_THROW(e.definition("Q", Prop(), Identifier("P")));
   ASSERT_ANY_THROW(e.type_of("R"));
}

TEST(Environment, Lookup)
{
   Environment e;
   e.definition("A", Type(), Prop());
   e.definition("B", Type(), Type());
   e.axiom("D", Type());
   expect_eq("eq-1", e.look_up("A"), Prop());
   expect_eq("eq-2", e.look_up("B"), Type());
   ASSERT_ANY_THROW(e.look_up("C"));
   expect_eq("eq-2", e.look_up("D"), Identifier("D"));
}

TEST(Environment, Modules)
{
   Environment e;
   e.modules.push_module("mod");
   e.axiom("A", Prop());
   expect_eq("eq-1", e.type_of(Name("mod", "A")), Prop());
   ASSERT_ANY_THROW(e.type_of(Name("mad", "A")));
   expect_eq("eq-2", normalize(e, Identifier("mod", "A")),
                     Identifier("mod", "A"));
   e.definition("B", Prop(), Identifier("mod", "A"));
}

TEST(Environment, ModulesSubstitution)
{
   Environment e;
   e.modules.push_module("mod");
   e.axiom("A", Prop());
   e.axiom("a", Identifier("A"));
   expect_eq("eq", e.type_of(Identifier("a")), Identifier("mod", "A"));
}

TEST(Environment, AliasForSort)
{
   Environment e;
   e.definition("Set", Type(), Type());
   e.axiom("S", Identifier("Set"));
   e.axiom("s", Identifier("S"));
}

TEST(TypeOf, Forall)
{
   Environment e;
   expect_eq("eq-1", type_of(e, Forall("P", Prop(), Identifier("P"))), Prop());
   ASSERT_ANY_THROW(type_of(e, Forall("P", Prop(), Identifier("Q"))));
   ASSERT_ANY_THROW(type_of(e, Identifier("P")));
   expect_eq("eq-2", type_of(e, Forall("P", Prop(), Prop())),
                     TypeMax(TypeSucc(Prop()), TypeSucc(Prop())));
   expect_eq("eq-3", type_of(e, Forall("P", Type(), Prop())),
                     TypeMax(TypeSucc(Type()), TypeSucc(Prop())));
   expect_eq("eq-4", type_of(e, Forall("P", Type(), Type())),
                     TypeMax(TypeSucc(Type()), TypeSucc(Type())));
}

TEST(TypeOf, ForallArgsHaveTypesInSort)
{
   Environment e;
   e.axiom("P", Prop());
   e.axiom("p", Identifier("P"));
   ASSERT_ANY_THROW(type_of(e, Forall("x", Identifier("p"), Prop())));
   ASSERT_ANY_THROW(type_of(e, Forall("x", Prop(), Identifier("p"))));
}

TEST(TypeOf, ForallVariableRename)
{
   Environment e;
   e.axiom("P", Prop());
   expect_eq("eq", type_of(e, Forall("P", Prop(), Identifier("P"))), Prop());
   expect_eq("eq", type_of(e, Forall("P", Type(), Identifier("P"))),
                   TypeMax(TypeSucc(Type()), Type()));
   ASSERT_ANY_THROW(type_of(e, Forall("P", Prop(), Identifier("P0"))));
}

TEST(TypeOf, Lambda)
{
   Environment e;
   expect_eq("eq-1", type_of(e, Lambda("P", Prop(), Identifier("P"))),
                     Forall("P", Prop(), Prop()));
   expect_eq("eq-2", type_of(e, Lambda("Q", Prop(), Identifier("Q"))),
                     Forall("Q", Prop(), Prop()));
   expect_eq("eq-3", type_of(e, Lambda("P", Type(), Identifier("P"))),
                     Forall("P", Type(), Type()));
}

TEST(TypeOf, LambdaVariableRename)
{
   Environment e;
   e.axiom("P", Prop());
   expect_eq("eq-1", type_of(e, Lambda("P", Prop(), Identifier("P"))),
      Forall("P0", Prop(), Prop()));
   expect_eq("eq-2",
      type_of(e, Lambda("P", Type(), Identifier("P"))),
      Forall("P0", Type(), Type()));
   ASSERT_ANY_THROW(type_of(e, Lambda("P", Prop(), Identifier("P0"))));
}

TEST(TypeOf, Apply)
{
   Environment e;
   ASSERT_ANY_THROW(type_of(e, Apply(Identifier("f"), Identifier("x"))));
   e.axiom("f", Forall("P", Prop(), Prop()));
   e.axiom("x", Prop());
   type_of(e, Apply(Identifier("f"), Identifier("x")));
   ASSERT_ANY_THROW(type_of(e, Apply(Identifier("x"), Identifier("f"))));
   ASSERT_ANY_THROW(type_of(e, Apply(Identifier("f"), Identifier("y"))));
   ASSERT_ANY_THROW(type_of(e, Apply(Identifier("f"), Prop())));
}

TEST(TypeOf, Apply2)
{
   Environment e;
   e.axiom("f", Forall("P", Type(), Type()));
   e.axiom("x", Type());
   expect_eq("eq", type_of(e, Apply(Identifier("f"), Identifier("x"))), Type());
}

TEST(TypeOfSubst, SameIdentifier)
{
   Environment e;
   e.axiom("f", Forall("P", Prop(), Identifier("P")));
   e.axiom("Q", Prop());
   expect_eq("eq", type_of(e, Apply(Identifier("f"), Identifier("Q"))),
      Identifier("Q"));
}

TEST(TypeOfSubst, OtherIdentifier)
{
   Environment e;
   e.axiom("Q", Prop());
   e.axiom("f", Forall("P", Prop(), Identifier("Q")));
   e.axiom("R", Prop());
   expect_eq("eq", type_of(e, Apply(Identifier("f"), Identifier("R"))),
      Identifier("Q"));
}

TEST(TypeOfSubst, ForallSubstType)
{
   Environment e;
   e.axiom("Q", Prop());
   e.axiom("f", Forall("P", Prop(), Forall("x", Identifier("P"), Prop())));
   e.axiom("R", Prop());
   expect_eq("eq", type_of(e, Apply(Identifier("f"), Identifier("R"))),
      Forall("x", Identifier("R"), Prop()));
}

TEST(TypeOfSubst, ForallSubstBody)
{
   Environment e;
   e.axiom("Q", Prop());
   e.axiom("f", Forall("P", Prop(), Forall("x", Prop(), Identifier("P"))));
   e.axiom("R", Prop());
   expect_eq("eq", type_of(e, Apply(Identifier("f"), Identifier("R"))),
      Forall("x", Prop(), Identifier("R")));
}

TEST(TypeOfSubst, VariableClash)
{
   Environment e;
   e.axiom("f", Forall("P", Prop(), Forall("Q", Prop(), Identifier("P"))));
   e.axiom("Q", Prop());
   expect_eq("eq", type_of(e, Apply(Identifier("f"), Identifier("Q"))),
      Forall("Q0", Prop(), Identifier("Q")));
}

TEST(TypeOfSubst, VariableSubstBody)
{
   Environment e;
   e.axiom("f", Forall("P", Prop(), Forall("Q", Prop(), Identifier("Q"))));
   e.axiom("Q", Prop());
   expect_eq("eq", type_of(e, Apply(Identifier("f"), Identifier("Q"))),
      Forall("Q", Prop(), Identifier("Q")));
}

TEST(TypeOfSubst, VariableClashFreeVariables)
{
   Environment e;
   e.axiom("f",
      Forall("P", Prop(),
         Forall("Q", Prop(), Forall("x", Identifier("P"), Identifier("Q")))));
   e.axiom("Q", Prop());
   e.axiom("Q1", Prop());
   expect_eq("eq",
      type_of(e,
         Apply(Identifier("f"),
            Forall("x", Identifier("Q"), Identifier("Q1")))),
      Forall("Q0", Prop(),
         Forall("x", Forall("x", Identifier("Q"), Identifier("Q1")),
            Identifier("Q0"))));
}

TEST(TypeOfSubst, VariableClashFreeVariablesTwice)
{
   Environment e;
   e.axiom("f",
      Forall("P", Prop(),
         Forall("Q", Prop(), Forall("x", Identifier("P"), Identifier("Q")))));
   e.axiom("Q", Prop());
   e.axiom("Q0", Prop());
   expect_eq("eq",
      type_of(e,
         Apply(Identifier("f"),
            Forall("x", Identifier("Q"), Identifier("Q0")))),
      Forall("Q1", Prop(),
         Forall("x", Forall("x", Identifier("Q"), Identifier("Q0")),
            Identifier("Q1"))));
}

TEST(TypeOfSubst, VariableDoesNotOccur)
{
   Environment e;
   e.axiom("f", Forall("Q0", Prop(), Forall("Q", Prop(), Identifier("Q"))));
   e.axiom("Q", Prop());
   expect_eq("eq",
      type_of(e, Apply(Identifier("f"), Identifier("Q"))),
      Forall("Q", Prop(), Identifier("Q")));
}

TEST(TypeOfSubst, DontRenameIntoVariableInBody)
{
   Environment e;
   e.axiom("f",
      Forall("Q0", Prop(),
         Forall("Q", Prop(), Forall("x", Identifier("Q"), Identifier("Q0")))));
   e.axiom("Q", Prop());
   expect_eq("eq",
      type_of(e, Apply(Identifier("f"), Identifier("Q"))),
      Forall("Q1", Prop(), Forall("x", Identifier("Q1"), Identifier("Q"))));
}

TEST(TypeOfSubst, ArgumentOfApply)
{
   Environment e;
   e.axiom("f", Forall("P", Prop(), Prop()));
   e.axiom("g", Forall("P", Prop(), Apply(Identifier("f"), Identifier("P"))));
   e.axiom("Q", Prop());
   expect_eq("eq",
      type_of(e, Apply(Identifier("g"), Identifier("Q"))),
      Apply (Identifier("f"), Identifier("Q")));
}

TEST(TypeOfSubst, FunctionOfApply)
{
   Environment e;
   e.axiom("P", Prop());
   e.axiom("g",
      Forall("f",
         Forall("x", Prop(), Prop()), Apply(Identifier("f"), Identifier("P"))));
   e.axiom("h", Forall("x", Prop(), Prop()));
   expect_eq("eq",
      type_of(e, Apply(Identifier("g"), Identifier("h"))),
      Apply(Identifier("h"), Identifier("P")));
}

TEST(TypeOfSubst, Lambda)
{
   Environment e;
   e.axiom("P", Prop());
   e.axiom("f",
      Forall("Q", Prop(),
         Apply(Lambda("R", Prop(), Identifier("Q")), Identifier("P"))));
   expect_eq("eq",
      type_of(e, Apply(Identifier("f"), Identifier("P"))),
      Apply(Lambda("R", Prop(), Identifier("P")), Identifier("P")));
}

void test_subst_lst(const Term &t, const SubstLst &lst, const Term &expected)
{
    Term result = t.ptr->subst_lst(lst);
    ASSERT_EQ(result, expected) << "substitution of " << t << " yielded "
        << result << " but was expected to yield " << expected;
}

TEST(SubstLst, Identifier)
{
    test_subst_lst(Identifier("A"), {}, Identifier("A"));
    test_subst_lst(Identifier("A"), {{ "A", Identifier("B") }},
                   Identifier("B"));
    test_subst_lst(Identifier("mod", "A"), {{ "A", Identifier("B") }},
                   Identifier("mod", "A"));
}

TEST(SubstLst, BindVariable)
{
    test_subst_lst(Forall("x", Prop(), Identifier("y")),
                   {{ "y", Identifier("z") }},
                   Forall("x", Prop(), Identifier("z")));
    test_subst_lst(Lambda("x", Prop(), Identifier("y")),
                   {{ "y", Identifier("z") }},
                   Lambda("x", Prop(), Identifier("z")));
    test_subst_lst(Lambda("x", Identifier("y"), Identifier("z")),
                   {{ "y", Identifier("t") }},
                   Lambda("x", Identifier("t"), Identifier("z")));
    test_subst_lst(Forall("x", Prop(),
                          Forall("_", Identifier("y"), Identifier("x"))),
                   {{ "y", Identifier("z") }, { "x", Identifier("t") }},
                   Forall("x", Prop(),
                          Forall("_", Identifier("z"), Identifier("x"))));
}

TEST(SubstLst, Apply)
{
    test_subst_lst(Apply(Identifier("x"), Identifier("y")),
                   { { "x", Identifier("a") }, { "y", Identifier("b") }},
                   Apply(Identifier("a"), Identifier("b")));
}

TEST(Normalize, Identifier)
{
   Environment e;
   e.definition("A", Type(), Type());
   expect_eq("eq-1", normalize(e, Prop()), Prop());
   expect_eq("eq-2", normalize(e, Identifier("A")), Type());
   expect_eq("eq-3",
      normalize(e, Forall("P", Identifier("A"), Identifier("A"))),
      Forall("P", Type(), Type()));
   expect_eq("eq-4",
      normalize(e, Lambda("P", Identifier("A"), Identifier("A"))),
      Lambda("P", Type(), Type()));
}

TEST(Normalize, ExpandTwice)
{
   Environment e;
   e.definition("A", Type(), Prop());
   e.definition("B", Type(), Identifier("A"));
   expect_eq("eq", normalize(e, Identifier("B")), Prop());
}

TEST(Normalize, RenameVariable)
{
   Environment e;
   e.modules.push_module("mod");
   e.axiom("A", Type());
   e.modules.pop_module();
   e.definition("A", Type(), Prop());
   expect_eq("eq-1",
      normalize(e, Forall("A", Identifier("A"), Identifier("A"))),
      Forall("A0", Prop(), Identifier("A0")));
   expect_eq("eq-2",
      normalize(e, Lambda("A", Identifier("A"), Identifier("A"))),
      Lambda("A0", Prop(), Identifier("A0")));
   expect_eq("eq-3",
      normalize(e, Lambda("A", Identifier("A"), Identifier("mod", "A"))),
      Lambda("A0", Prop(), Identifier("mod", "A")));
}

TEST(Normalize, Apply)
{
   Environment e;
   e.definition("A", Type(), Prop());
   e.axiom("f", Forall("_", Prop(), Prop()));
   expect_eq("eq",
      normalize(e, Apply(Identifier("f"), Identifier("A"))),
      Apply(Identifier("f"), Prop()));
}

TEST(Normalize, ApplyFunction)
{
   Environment e;
   e.axiom("A", Prop());
   e.axiom("f", Forall("_", Prop(), Prop()));
   e.definition("g", Forall("_", Prop(), Prop()), Identifier("f"));
   expect_eq("eq",
      normalize(e, Apply(Identifier("g"), Identifier("A"))),
      Apply(Identifier("f"), Identifier("A")));
}

TEST(Normalize, BetaReduction)
{
   Environment e;
   e.axiom("A", Prop());
   expect_eq("eq",
      normalize(e,
         Apply(Lambda("P", Prop(),
                      Forall("_", Identifier("P"), Identifier("P"))),
               Identifier("A"))),
      Forall("_", Identifier("A"), Identifier("A")));
}

TEST(Normalize, Definition)
{
   Environment e;
   e.definition("Set", Type(), Type());
   e.axiom("S", Identifier("Set"));
   e.definition("P", Type(), Identifier("S"));
}

TEST(HeadReduce, Identifier)
{
   Environment e;
   e.axiom("Q", Prop());
   expect_eq("eq", head_reduce(e, Identifier("Q")), Identifier("Q"));
}

TEST(HeadReduce, ExpandDefinitions)
{
   Environment e;
   e.axiom("P", Prop());
   e.definition("Q", Prop(), Identifier("P"));
   e.definition("R", Prop(), Identifier("Q"));
   expect_eq("eq-1", head_reduce(e, Identifier("P")), Identifier("P"));
   expect_eq("eq-2", head_reduce(e, Identifier("Q")), Identifier("P"));
   expect_eq("eq-2", head_reduce(e, Identifier("R")), Identifier("P"));
}

TEST(HeadReduce, Apply)
{
   Environment e;
   e.axiom("P", Forall("P", Prop(), Prop()));
   e.definition("Q", Forall("P", Prop(), Prop()), Identifier("P"));
   e.axiom("R", Prop());
   expect_eq("eq-1", head_reduce(e, Apply(Identifier("Q"), Identifier("R"))),
                                    Apply(Identifier("P"), Identifier("R")));
   expect_eq("eq-2",
      head_reduce(e,
         Apply(Lambda("P", Prop(), Identifier("P")), Identifier("R"))),
      Identifier("R"));
}

TEST(ReductionEqual, Equal)
{
   Environment e;
   e.axiom("P", Prop());
   e.axiom("Q", Prop());
   EXPECT_TRUE(red_equal(e, Identifier("P"), Identifier("P")));
   EXPECT_FALSE(red_equal(e, Identifier("P"), Identifier("Q")));
   EXPECT_FALSE(red_equal(e, Forall("R", Prop(), Identifier("P")),
                             Forall("R", Prop(), Identifier("Q"))));
}

TEST(ReductionEqual, LookupIdentifier)
{
   Environment e;
   e.axiom("P", Prop());
   e.definition("Q", Prop(), Identifier("P"));
   EXPECT_TRUE(red_equal(e, Identifier("P"), Identifier("Q")));
   EXPECT_TRUE(red_equal(e, Identifier("Q"), Identifier("P")));
   EXPECT_FALSE(red_equal(e, Forall("a", Prop(), Prop()),
                             Forall("a", Identifier("Q"), Prop())));
   EXPECT_TRUE(red_equal(e, Forall("a", Identifier("P"), Prop()),
                            Forall("a", Identifier("Q"), Prop())));
   EXPECT_TRUE(red_equal(e, Forall("R", Prop(), Identifier("P")),
                            Forall("R", Prop(), Identifier("Q"))));
   EXPECT_TRUE(red_equal(e, Lambda("a", Identifier("P"), Identifier("a")),
                            Lambda("b", Identifier("Q"), Identifier("b"))));
   EXPECT_TRUE(red_equal(e, Forall("P", Identifier("P"), Identifier("P")),
                            Forall("Q", Identifier("Q"), Identifier("Q"))));
}

TEST(ReductionEqual, Modules)
{
    Environment e;
    e.modules.push_module("mad");
    e.modules.push_module("mod");
    e.definition("a", Type(), Type());
    e.modules.pop_module();
    e.modules.pop_module();
    EXPECT_TRUE(red_equal(e, Identifier("mod", "a"), Type()));
    EXPECT_TRUE(red_equal(e, Type(), Identifier("mod", "a")));
}

TEST(ReductionEqual, Apply)
{
   Environment e;
   e.axiom("P", Forall("P", Prop(), Prop()));
   e.axiom("Q", Prop());
   e.definition("R", Prop(), Identifier("Q"));
   EXPECT_TRUE(
      red_equal(e,
         Apply(Lambda("P", Prop(), Identifier("P")), Identifier("Q")),
         Identifier("Q")));
   EXPECT_TRUE(
      red_equal(e,
         Identifier("Q"),
         Apply(Lambda("P", Prop(), Identifier("P")), Identifier("Q"))));
   EXPECT_TRUE(red_equal(e, Apply(Identifier("P"), Identifier("Q")),
                            Apply(Identifier("P"), Identifier("R"))));
}

TEST(Subtyping, AcceptSubtypeArg)
{
    Environment e;
    e.axiom("P", Forall("P", Type(), Type()));
    e.axiom("Q", Prop());
    expect_eq("eq", type_of(e, Apply(Identifier("P"), Identifier("Q"))), Type());
}

TEST(Subtyping, AcceptSubtypeArg2)
{
    Environment e;
    e.axiom("P", Forall("P", Type(), Type()));
    e.axiom("Q", Type());
    expect_eq("eq", type_of(e, Apply(Identifier("P"), Identifier("Q"))), Type());
}

TEST(Subtyping, AcceptSubtypeArg3)
{
    Environment e;
    e.axiom("P", Forall("P", Forall("Q", Type(), Type()), Type()));
    e.axiom("Q", Forall("P", Type(), Prop()));
    expect_eq("eq", type_of(e, Apply(Identifier("P"), Identifier("Q"))),  Type());
}

TEST(Subtyping, AcceptSubtypeArg4)
{
    Environment e;
    e.axiom("A", Prop());
    e.definition("B", Type(), Identifier("A"));
}

TEST(UniverseLevels, SameTypeError1)
{
    Environment e;
    e.definition("A", Type(), Type());
    ASSERT_ANY_THROW(e.definition("B", Identifier("A"), Identifier("A")));
}

TEST(UniverseLevels, SameTypeError2)
{
    Environment e;
    e.definition("A", Type(), Type());
    ASSERT_ANY_THROW(
       e.definition(
          "B",
          Identifier("A"),
          Forall("x", Identifier("A"), Prop())));
}

TEST(UniverseLevels, CyclicalTypeError)
{
    Environment e;
    e.definition("A", Type(), Type());
    e.definition("B", Type(), Type());
    e.definition("C", Identifier("A"), Identifier("B"));
    ASSERT_ANY_THROW(e.definition("D", Identifier("B"), Identifier("A")));
}

TEST(UniverseLevels, CyclicalTypeError2)
{
    Environment e;
    e.definition("A", Type(), Type());
    e.definition("B", Type(), Type());
    e.definition("C", Type(), Type());
    e.definition("D", Identifier("B"), Identifier("A"));
    e.definition("E", Identifier("C"), Identifier("B"));
    ASSERT_ANY_THROW(e.definition("F", Identifier("B"), Identifier("C")));
}

TEST(UniverseLevels, CyclicalTypeError3)
{
    Environment e;
    e.definition("equal_type", Type(),
        Forall("T", Type(),
            Forall("t1", Identifier("T"), Forall("t2", Identifier("T"), Prop()))));
    e.axiom("equal", Identifier("equal_type"));
    ASSERT_ANY_THROW(
        e.definition("Q",
            Forall("H", Identifier("equal_type"), Prop()),
            Apply(Apply(Identifier("equal"), Identifier("equal_type")),
                  Identifier("equal"))));
}

int main(int argc, char **argv)
{
   testing::InitGoogleTest(&argc, argv);
   return RUN_ALL_TESTS();
}

