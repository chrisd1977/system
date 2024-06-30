#pragma once
#include "system.h"
#include <memory>
#include <vector>
#include <iosfwd>
#include <string>

class BasicVisitor;

typedef std::vector<std::pair<HString, Term>> SubstLst;

class Basic: public std::enable_shared_from_this<Basic>
{
public:
   virtual ~Basic() = default;
   virtual std::shared_ptr<const Basic> clone() const = 0;
   virtual bool is_equal(const Basic &other) const = 0;
   virtual bool is_a_sort() const;
   virtual Term type_of(Environment &e) const = 0;
   virtual void visit(BasicVisitor &v) const = 0;
   virtual bool red_compare(Environment &e, const Basic &other, CompareKind kind) const;
   virtual VariableVector free_variables() const;
   virtual Term subst(HString var, const Term &t) const;
   virtual Term subst_lst(const SubstLst &l) const;
   virtual Term normalize(Environment &e) const;
};

class Identifier: public Basic, public Name
{
public:
   Identifier(HString name);
   Identifier(HString module_name, HString name);
   virtual std::shared_ptr<const Basic> clone() const override;
   bool is_equal(const Basic &other) const override;
   Term type_of(Environment &e) const override;
   void visit(BasicVisitor &v) const override;
   VariableVector free_variables() const override;
   Term subst(HString var, const Term &t) const override;
   Term subst_lst(const SubstLst &l) const override;
   Term normalize(Environment &e) const override;
};

class Prop: public Basic
{
public:
   virtual std::shared_ptr<const Basic> clone() const override;
   bool is_equal(const Basic &other) const override;
   virtual bool is_a_sort() const override;
   Term type_of(Environment &e) const override;
   void visit(BasicVisitor &v) const override;
};

class Type: public Basic
{
public:
   virtual std::shared_ptr<const Basic> clone() const override;
   bool is_equal(const Basic &other) const override;
   virtual bool is_a_sort() const override;
   Term type_of(Environment &e) const override;
   bool red_compare(Environment &e, const Basic &other, CompareKind kind) const override;
   void visit(BasicVisitor &v) const override;
};

class TypeSucc: public Basic
{
public:
   TypeSucc(Term t);
   std::shared_ptr<const Basic> clone() const override;
   bool is_equal(const Basic &other) const override;
   virtual bool is_a_sort() const override;
   Term type_of(Environment &e) const override;
   void visit(BasicVisitor &v) const override;
public:
   Term arg;
};

class TypeMax: public Basic
{
public:
   TypeMax(Term arg1, Term arg2);
   std::shared_ptr<const Basic> clone() const override;
   bool is_equal(const Basic &other) const override;
   virtual bool is_a_sort() const override;
   Term type_of(Environment &e) const override;
   void visit(BasicVisitor &v) const override;
public:
   Term arg1;
   Term arg2;
};

class BindVariable: public Basic
{
public:
   BindVariable(HString var, const Term &type, const Term &body);
   bool is_equal(const Basic &other) const override;
   bool red_compare(Environment &e, const Basic &other, CompareKind kind) const override;
   VariableVector free_variables() const override;
   Term try_type_of_name_collision(Environment &e) const;
   Term subst(HString var, const Term &t) const override;
   Term subst_lst(const SubstLst &l) const override;
   Term normalize(Environment &e) const override;
private:
   std::shared_ptr<const Basic> create_same_type(
      HString var, const Term &type, const Term &body) const;
   std::shared_ptr<const Basic> replace_fields(
      std::shared_ptr<const Basic> new_type,
      std::shared_ptr<const Basic> new_body) const;
public:
   HString var;
   Term type;
   Term body;
};

class Forall: public BindVariable
{
public:
   Forall(HString var, const Term &type, const Term &body);
   virtual std::shared_ptr<const Basic> clone() const override;
   Term type_of(Environment &e) const override;
   void visit(BasicVisitor &v) const override;
};

class Lambda: public BindVariable
{
public:
   Lambda(HString var, const Term &type, const Term &body);
   virtual std::shared_ptr<const Basic> clone() const override;
   Term type_of(Environment &e) const override;
   void visit(BasicVisitor &v) const override;
};

class Apply: public Basic
{
public:
   Apply(const Term &function, const Term &argument);
   virtual std::shared_ptr<const Basic> clone() const override;
   bool is_equal(const Basic &other) const override;
   Term type_of(Environment &e) const override;
   void visit(BasicVisitor &v) const override;
   bool red_compare(Environment &e, const Basic &other, CompareKind kind) const override;
   VariableVector free_variables() const override;
   Term subst(HString var, const Term &t) const override;
   Term subst_lst(const SubstLst &l) const override;
   Term normalize(Environment &e) const override;
private:
   std::shared_ptr<const Basic> replace_fields(
      std::shared_ptr<const Basic> new_fun,
      std::shared_ptr<const Basic> new_arg) const;
public:
   Term function;
   Term argument;
};

