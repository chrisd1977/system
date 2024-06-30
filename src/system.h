#pragma once
#include "hstring.h"
#include <memory>
#include <vector>
#include <iosfwd>
#include <string>

class Basic;
class Type;

class Term
{
public:
   Term(const Basic &t);
   Term(std::shared_ptr<const Basic> t = nullptr);
   bool operator==(const Term &t) const;
   bool operator!=(const Term &t) const;
   template <class T>
   bool is_a() const
   {
      return typeid(*ptr) == typeid(T);
   }
   bool is_a_sort() const;
   const std::type_info &get_term_type() const;
public:
   const std::shared_ptr<const Basic> ptr;
};

std::ostream &operator<<(std::ostream &os, const Term &t);

struct Name
{
public:
   Name(HString name);
   Name(HString module_name, HString name);
   Name(const char *name);
   Name(const char *module_name, const char *name);
   bool operator==(Name other) const;
   bool operator<(Name other) const;
public:
   HString module_name;
   HString name;
};

std::ostream &operator<<(std::ostream &os, const Name &name);

typedef std::vector<HString> VariableVector;

std::ostream &operator<<(std::ostream &os, const VariableVector &name);

typedef std::vector<std::pair<HString, Term>> SubstLst;

struct Definition 
{
   Definition(const Name& name, const Term& type, const Term& value);
   Name name;
   Term type;
   Term value;
};

class ModuleLevel
{
public:
    ModuleLevel(HString name = hstring_empty);
    HString module_name() const;
    bool is_a_direct_import(HString name) const;
    bool is_an_indirect_import(HString name) const;
    void add_module_contents(const ModuleLevel &lev);
private:
    HString name;
    std::vector<HString> direct_imports;
    std::vector<HString> indirect_imports;
};

struct ModuleInfo
{
public:
    ModuleInfo();
    HString top_level_module() const;
    bool is_a_direct_import(HString name) const;
    bool is_an_indirect_import(HString name) const;
    void push_module(HString name);
    void pop_module();
    bool import_module(HString name);
private:
    std::vector<ModuleLevel> stored_modules;
    std::vector<ModuleLevel> module_stack;
};

typedef std::vector<std::pair<const Type*, const Type*>> Constraints;

class Universes
{
public:
    void add_lt(const Type *t1, const Type *t2);
private:
    typedef std::vector<const Type*> Types;
    Types find_lowest_types(Constraints::iterator begin);
    Constraints::iterator partition_lowest(
       Constraints::iterator begin, Types &lowest_types);
private:
    Constraints constraints;
};

class Environment
{
public:
   void axiom(HString name, const Term &type, bool in_module = true);
   void definition(HString name, const Term &type, const Term &body);
   void pop();
   Term type_of(const Name &name) const;
   Term look_up(const Name &name) const;
   bool has_name(HString name) const;
   VariableVector get_globals() const;
public:
   ModuleInfo modules;
   Universes universes;
private:
   typedef std::vector<Definition> Definitions;
   Definitions::const_reverse_iterator lookup_iterator(
      const Name &name, bool throw_on_not_found, bool add_module_name) const;
   SubstLst create_subst_lst(const VariableVector &variables);
   void add(const Name &name, const Term &type, const Term &value);
   void check_for_axiom(HString name, const Term &type);
   void check_for_definition(const Term &type, const Term &body);
private:
   Definitions definitions;
};

Term type_of(Environment &e, const Term &t);

VariableVector free_variables(const Term &t);

void add_to_variables(VariableVector &v, HString name);

VariableVector merge_variable_vectors(const VariableVector &v1,
                                      const VariableVector &v2);

HString new_variable(HString var, const VariableVector& in_use);

Term normalize(Environment &e, const Term &t);

Term head_reduce(Environment &e, const Term &t);

enum class CompareKind { EQ, LE };

bool red_compare(Environment &e, const Term &t1, const Term &t2, CompareKind kind);

inline bool red_equal(Environment &e, const Term &t1, const Term &t2)
{
    return red_compare(e, t1, t2, CompareKind::EQ);
}

