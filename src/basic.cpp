#include "temporary_axiom.h"
#include "basic_visitor.h"
#include "throw_runtime_error.h"
#include <algorithm>
#include <ostream>

/*****************
 * Basic methods *
 *****************/

bool Basic::is_a_sort() const
{
   return false;
}

bool Basic::red_compare(Environment &e, const Basic &other, CompareKind kind) const
{
   return false;
}

VariableVector Basic::free_variables() const
{
   return {};
}

Term Basic::subst(HString var, const Term &t) const
{
   return shared_from_this();
}

Term Basic::subst_lst(const SubstLst&) const
{
    return shared_from_this();
}

Term Basic::normalize(Environment &e) const
{
   return shared_from_this();
}

/**********************
 * Identifier methods *
 **********************/

Identifier::Identifier(HString name): Name(name) {}

Identifier::Identifier(HString module_name, HString name):
   Name(module_name, name) {}

std::shared_ptr<const Basic> Identifier::clone() const
{
   return std::make_shared<Identifier>(module_name, name);
}

bool Identifier::is_equal(const Basic &other) const
{
   return module_name == ((const Identifier&)other).module_name
      && name == ((const Identifier&)other).name;
}

Term Identifier::type_of(Environment &e) const
{
   return e.type_of(*this);
}

void Identifier::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

VariableVector Identifier::free_variables() const
{
   return module_name.empty() ? VariableVector { name } : VariableVector {};
}

Term Identifier::subst(HString var, const Term &t) const
{
   if (module_name.empty() && var == name)
      return t;
   return shared_from_this();
}

Term Identifier::subst_lst(const SubstLst &l) const
{
   if (module_name.empty())
      for (const auto &p: l)
         if (name == p.first)
            return p.second;
   return shared_from_this();
}

Term Identifier::normalize(Environment &e) const
{
   Term result = e.look_up(*this);
   Term this_term = shared_from_this();
   if (this_term == result)
      return this_term;
   else
      return result;
}

/****************
 * Prop methods *
 ****************/

std::shared_ptr<const Basic> Prop::clone() const
{
   return std::make_shared<Prop>();
}

bool Prop::is_a_sort() const
{
   return true;
}

bool Prop::is_equal(const Basic &t) const
{
   return true;
}

Term Prop::type_of(Environment &e) const
{
   return Term(std::make_shared<TypeSucc>(shared_from_this()));
}

void Prop::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

/****************
 * Type methods *
 ****************/

std::shared_ptr<const Basic> Type::clone() const
{
   return std::make_shared<Type>();
}

bool Type::is_a_sort() const
{
   return true;
}

bool Type::is_equal(const Basic &t) const
{
   return true;
}

Term Type::type_of(Environment &e) const
{
   return Term(std::make_shared<const TypeSucc>(shared_from_this()));
}

bool Type::red_compare(Environment &e, const Basic &other, CompareKind kind) const
{
    return true;
}

void Type::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

/********************
 * TypeSucc methods *
 ********************/

TypeSucc::TypeSucc(Term arg): arg(arg) {}

std::shared_ptr<const Basic> TypeSucc::clone() const
{
   return std::make_shared<const TypeSucc>(arg);
}

bool TypeSucc::is_a_sort() const
{
   return true;
}

bool TypeSucc::is_equal(const Basic &other) const
{
   TypeSucc &other_ts = (TypeSucc&)other;
   return arg == other_ts.arg;
}

Term TypeSucc::type_of(Environment &e) const
{
   throw std::runtime_error("type_of of TypeSucc is not implemented");
}

void TypeSucc::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

/*******************
 * Typemax methods *
 *******************/

TypeMax::TypeMax(Term arg1, Term arg2): arg1(std::move(arg1)), arg2(std::move(arg2)) {}

std::shared_ptr<const Basic> TypeMax::clone() const
{
   return std::make_shared<const TypeMax>(arg1, arg2);
}

bool TypeMax::is_a_sort() const
{
   return true;
}

bool TypeMax::is_equal(const Basic &other) const
{
   const TypeMax &other_tm = (const TypeMax&)other;
   return arg1 == other_tm.arg1 && arg2 == other_tm.arg2;
}

Term TypeMax::type_of(Environment &e) const
{
   throw std::runtime_error("type_of of TypeMax is not implemented");
}

void TypeMax::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

/************************
 * BindVariable methods *
 ************************/

BindVariable::BindVariable(HString var, const Term &type, const Term &body):
   var(var), type(type), body(body) {}

bool BindVariable::is_equal(const Basic &other) const
{
   BindVariable &other_bv = (BindVariable&)other;
   if (type != other_bv.type)
      return false;
   if (var == other_bv.var)
      return body == other_bv.body;
   VariableVector free = ::free_variables(other_bv.body);
   if (find(free.begin(), free.end(), var) != free.end())
      return false;
   return body == other_bv.body.ptr->subst(other_bv.var, Identifier(var));
}

bool BindVariable::red_compare(Environment &e, const Basic &other, CompareKind kind) const
{
   const BindVariable &other_bv = (const BindVariable&)other;
   if (!::red_equal(e, type, other_bv.type))
      return false;
   HString new_var = var;
   std::shared_ptr<const Basic> new_body = body.ptr;
   if (e.has_name(var))
   {
      new_var = new_variable(var, e.get_globals());
      new_body = body.ptr->subst(var, Identifier(new_var)).ptr;
   }
   std::shared_ptr<const Basic> other_body = other_bv.body.ptr;
   if (other_bv.var != new_var)
      other_body = other_body->subst(other_bv.var, Identifier(new_var)).ptr;
   TemporaryAxiom ax(e, new_var, type);
   if (typeid(*this) == typeid(Forall))
      return ::red_compare(e, new_body, other_body, kind);
   else
      return ::red_equal(e, new_body, other_body);
}

VariableVector BindVariable::free_variables() const
{
   VariableVector from_type = type.ptr->free_variables();
   VariableVector from_body = body.ptr->free_variables();
   VariableVector::iterator end
      = remove(from_body.begin(), from_body.end(), var);
   from_body.erase(end, from_body.end());
   return merge_variable_vectors(from_type, from_body);
}

Term BindVariable::try_type_of_name_collision(Environment &e) const
{
   if (e.has_name(var))
   {
      HString new_var
         = new_variable(var,
            merge_variable_vectors(e.get_globals(), ::free_variables(body)));
      Term new_body = body.ptr->subst(var, Identifier(new_var));
      return create_same_type(new_var, type, new_body)->type_of(e);
   }
   return Term();
}

Term BindVariable::subst(HString var, const Term &t) const
{
   VariableVector free_of_this = free_variables();
   if (find(free_of_this.begin(), free_of_this.end(), var)
          == free_of_this.end())
      return shared_from_this();
   VariableVector free_of_subs = ::free_variables(t);
   HString new_var = this->var;
   if (find(free_of_subs.begin(), free_of_subs.end(), this->var)
         != free_of_subs.end())
      new_var = new_variable(new_var,
                   merge_variable_vectors(free_of_this, free_of_subs));
   Term subst_type = type.ptr->subst(var, t);
   std::shared_ptr<const Basic> subst_body = body.ptr;
   if (new_var != this->var)
      subst_body = subst_body->subst(this->var, Identifier(new_var)).ptr;
   subst_body = subst_body->subst(var, t).ptr;
   return create_same_type(new_var, subst_type, subst_body);
}

// This does not check whether rhses of substitutions contain the bound
// variable. This is not necessary if we only use subst_lst for the
// substitution of Identifiers without module for Identifiers with module.
Term BindVariable::subst_lst(const SubstLst &l) const
{
   SubstLst new_list;
   SubstLst::const_iterator it = std::find_if(l.begin(), l.end(),
      [this](SubstLst::value_type p)
      {
         return p.first == var;
      });
   if (it != l.end())
   {
      new_list.reserve(l.size() - 1);
      for_each(l.begin(), it,
         [&](SubstLst::value_type p) { new_list.emplace_back(p); });
      for_each(it + 1, l.end(),
         [&](SubstLst::value_type p) { new_list.emplace_back(p); });
   }
   Term new_type = type.ptr->subst_lst(l);
   Term new_body = body.ptr->subst_lst(it == l.end() ? l : new_list);
   return replace_fields(new_type.ptr, new_body.ptr);
}

Term BindVariable::normalize(Environment &e) const
{
   if (e.has_name(var))
   {
      HString new_name = new_variable(var, e.get_globals());
      Term new_body = body.ptr->subst(var,
                               Term(std::make_shared<Identifier>(new_name)));
      return ::normalize(e, create_same_type(new_name, type, new_body));
   }
   Term new_type = ::normalize(e, type);
   TemporaryAxiom ax(e, var, new_type);
   Term new_body = ::normalize(e, body);
   return replace_fields(new_type.ptr, new_body.ptr);
}

std::shared_ptr<const Basic> BindVariable::create_same_type(
      HString var, const Term &type, const Term &body) const
{
   if (typeid(*this) == typeid(Forall))
      return std::make_shared<Forall>(var, type, body);
   else
      return std::make_shared<Lambda>(var, type, body);
}

std::shared_ptr<const Basic> BindVariable::replace_fields(
      std::shared_ptr<const Basic> new_type, 
      std::shared_ptr<const Basic> new_body) const
{
   if (new_type == type.ptr && new_body == body.ptr)
      return shared_from_this();
   return create_same_type(var, new_type, new_body);
}
   
/******************
 * Forall methods *
 ******************/

Forall::Forall(HString var, const Term &type, const Term &body):
   BindVariable(var, type, body) {}

std::shared_ptr<const Basic> Forall::clone() const
{
   return std::make_shared<Forall>(var, type, body);
}

Term Forall::type_of(Environment &e) const
{
   Term result = try_type_of_name_collision(e);
   if (result.ptr)
      return result;
   Term t2 = ::type_of(e, type);
   TemporaryAxiom ax(e, var, type);
   Term t1 = ::normalize(e, ::type_of(e, body));
   if (!t1.is_a_sort())
      ThrowRuntimeError()
         << "body of a forall should have a type that is a sort but got "
         << body << " instead which is of type " << t1;
   if (t1.is_a<Prop>())
      return t1;
   return Term(std::make_shared<TypeMax>(t2, t1));
}

void Forall::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

/******************
 * Lambda methods *
 ******************/

Lambda::Lambda(HString var, const Term &type, const Term &body):
   BindVariable(var, type, body) {}

std::shared_ptr<const Basic> Lambda::clone() const
{
   return std::make_shared<Lambda>(var, type, body);
}

Term Lambda::type_of(Environment &e) const
{
   Term result = try_type_of_name_collision(e);
   if (result.ptr)
      return result;
   Term t2 = ::type_of(e, type);
   TemporaryAxiom ax(e, var, type);
   Term t1 = ::type_of(e, body);
   return Term(std::make_shared<Forall>(var, type, t1));
}

void Lambda::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

/***************
 * Apply class *
 ***************/

Apply::Apply(const Term &function, const Term &argument):
   function(function), argument(argument) {}

std::shared_ptr<const Basic> Apply::clone() const
{
   return std::make_shared<Apply>(function, argument);
}

bool Apply::is_equal(const Basic &other) const
{
   Apply &other_apply = (Apply&)other;
   return function == other_apply.function && argument == other_apply.argument;
}

Term Apply::type_of(Environment &e) const
{
   Term type_of_function = ::head_reduce(e, ::type_of(e, function));
   if (!type_of_function.is_a<Forall>())
      ThrowRuntimeError()
         << "left hand side of an apply should be a forall term but "
         << function << " has type " << type_of_function << " instead";
   Term type_of_argument = ::type_of(e, argument);
   Forall *forall = (Forall*)(type_of_function.ptr.get());
   if (!::red_compare(e, type_of_argument, forall->type, CompareKind::LE))
      ThrowRuntimeError()
         << "right hand side of apply should be of type " << forall->type
         << " but was found to be " << type_of_argument << " instead";
   return forall->body.ptr->subst(forall->var, argument);
}

void Apply::visit(BasicVisitor &v) const
{
   v.accept(*this);
}

bool Apply::red_compare(Environment &e, const Basic &other, CompareKind kind) const
{
   const Apply &other_apply = (const Apply&)other;
   return ::red_equal(e, function, other_apply.function)
      && ::red_equal(e, argument, other_apply.argument);
}

VariableVector Apply::free_variables() const
{
   return merge_variable_vectors(function.ptr->free_variables(),
                                 argument.ptr->free_variables());
}

Term Apply::subst(HString var, const Term &t) const
{
   Term function_subst = function.ptr->subst(var, t);
   Term argument_subst = argument.ptr->subst(var, t);
   return replace_fields(function_subst.ptr, argument_subst.ptr);
}

Term Apply::subst_lst(const SubstLst &l) const
{
   Term function_subst = function.ptr->subst_lst(l);
   Term argument_subst = argument.ptr->subst_lst(l);
   return replace_fields(function_subst.ptr, argument_subst.ptr);
}

Term Apply::normalize(Environment &e) const
{
   Term new_argument = ::normalize(e, argument);
   if (function.is_a<Lambda>())
   {
      std::shared_ptr<const Lambda> lhs
         = std::dynamic_pointer_cast<const Lambda>(function.ptr);
      return lhs->body.ptr->subst(lhs->var, new_argument);
   }
   Term new_function = ::normalize(e, function);
   return replace_fields(new_function.ptr, new_argument.ptr);
}

std::shared_ptr<const Basic> Apply::replace_fields(
      std::shared_ptr<const Basic> new_fun,
      std::shared_ptr<const Basic> new_arg) const
{
   if (new_fun == function.ptr && new_arg == argument.ptr)
      return shared_from_this();
   return std::make_shared<Apply>(new_fun, new_arg);
}

