#include "throw_runtime_error.h"
#include "basic.h"
#include "system.h"
#include <algorithm>
#include <ostream>

/****************
 * Term methods *
 ****************/

Term::Term(const Basic &t): ptr(t.clone()) {}

Term::Term(std::shared_ptr<const Basic> t): ptr(t) {}

bool Term::operator==(const Term &t) const
{
   if (typeid(*ptr) != typeid(*t.ptr))
      return false;
   return ptr->is_equal(*t.ptr);
}

bool Term::operator!=(const Term &t) const
{
   return !(*this == t);
}

bool Term::is_a_sort() const
{
   return ptr->is_a_sort();
}

const std::type_info &Term::get_term_type() const
{
    return typeid(*ptr);
}

/****************
 * Name methods *
 ****************/

Name::Name(HString name): module_name(hstring_empty), name(name) {}

Name::Name(HString module_name, HString name):
   module_name(module_name), name(name) {}

Name::Name(const char *name): module_name(hstring_empty), name(name) {}

Name::Name(const char *module_name, const char *name):
   module_name(module_name), name(name) {}

bool Name::operator==(Name other) const
{
   return module_name == other.module_name && name == other.name;
}

bool Name::operator<(Name other) const
{
   if (module_name < other.module_name)
      return true;
   if (other.module_name < module_name)
      return false;
   return name < other.name;
}

std::ostream &operator<<(std::ostream &os, const Name &name)
{
   return os << name.module_name << "." << name.name;
}

std::ostream &operator<<(std::ostream &os, const VariableVector &v)
{
   os << "{ ";
   bool first = true;
   for (HString n: v)
   {
      if (!first)
         os << ", ";
      os << n;
      first = false;
   }
   return os << " }";
}

/**********************
 * Definition methods *
 **********************/

Definition::Definition(const Name& name, const Term& type, const Term& value):
   name(name), type(type), value(value) {}

/***********************
 * ModuleLevel methods *
 ***********************/

ModuleLevel::ModuleLevel(HString name): name(name) {}

HString ModuleLevel::module_name() const
{
    return name;
}

bool ModuleLevel::is_a_direct_import(HString name) const
{
   return find(direct_imports.begin(), direct_imports.end(), name)
      != direct_imports.end();
}

bool ModuleLevel::is_an_indirect_import(HString name) const
{
   return find(indirect_imports.begin(), indirect_imports.end(), name)
      != indirect_imports.end();
}

void ModuleLevel::add_module_contents(const ModuleLevel &lev)
{
   add_to_variables(direct_imports, lev.name);
   VariableVector imports
        = merge_variable_vectors(lev.direct_imports, lev.indirect_imports);
   indirect_imports = merge_variable_vectors(indirect_imports, imports);
}

/**********************
 * ModuleInfo methods *
 **********************/

ModuleInfo::ModuleInfo(): module_stack(1) {}

HString ModuleInfo::top_level_module() const
{
    return module_stack.back().module_name();
}

bool ModuleInfo::is_a_direct_import(HString name) const
{
   return module_stack.back().is_a_direct_import(name);
}

bool ModuleInfo::is_an_indirect_import(HString name) const
{
   return module_stack.back().is_an_indirect_import(name);
}

void ModuleInfo::push_module(HString name)
{
   module_stack.emplace_back(name);
}

void ModuleInfo::pop_module()
{
   stored_modules.push_back(module_stack.back());
   module_stack.pop_back();
   module_stack.back().add_module_contents(stored_modules.back());
}

bool ModuleInfo::import_module(HString name)
{
   for (const ModuleLevel &mod: stored_modules)
      if (mod.module_name() == name)
      {
         module_stack.back().add_module_contents(mod);
         return true;
      }
    return false;
}

/*********************
 * Universes methods *
 *********************/

Universes::Types Universes::find_lowest_types(Constraints::iterator begin)
{
   Types left_types;
   Types right_types;
   left_types.reserve(constraints.size());
   right_types.reserve(constraints.size());
   for (Constraints::iterator it = begin; it != constraints.end(); ++it)
   {
      left_types.push_back(it->first);
      right_types.push_back(it->second);
   }
   std::sort(left_types.begin(), left_types.end());
   std::sort(right_types.begin(), right_types.end());
   Types::iterator new_end_left = std::unique(left_types.begin(), left_types.end());
   Types::iterator new_end_right = std::unique(right_types.begin(), right_types.end());
   Types difference;
   std::set_difference(left_types.begin(), new_end_left, right_types.begin(), new_end_right,
                       std::inserter(difference, difference.begin()));
   if (difference.empty())
      throw std::runtime_error("Universe inconsistency");
   return difference;
}

Constraints::iterator
      Universes::partition_lowest(Constraints::iterator begin, Types &lowest_types)
{
   return std::partition(begin, constraints.end(),
      [&lowest_types](Constraints::value_type p)
      {
         return std::find_if(lowest_types.begin(), lowest_types.end(),
               [p](const Type *t)
               {
                  return p.first == t;
               })
            != lowest_types.end();
      });
}

void Universes::add_lt(const Type *t1, const Type *t2)
{
   if (!t1 || !t2)
      return;
   if (std::find(constraints.begin(), constraints.end(), std::make_pair(t1, t2))
         != constraints.end())
      return;
   constraints.push_back(std::make_pair(t1, t2));

   for (Constraints::iterator it = constraints.begin(); it != constraints.end();)
   {
      Types lowest_types = find_lowest_types(it);
      it = partition_lowest(it, lowest_types);
   }
}

/***********************
 * Environment methods *
 ***********************/

void Environment::axiom(HString name, const Term &type, bool in_module)
{
   SubstLst subses = create_subst_lst(free_variables(type));
   Term subst_type = type.ptr->subst_lst(subses);
   check_for_axiom(name, subst_type);
   Identifier full_name(in_module ? modules.top_level_module() : hstring_empty,
                        name);
   add(full_name, subst_type, full_name);
}

void Environment::definition(HString name, const Term &type, const Term &body)
{
   VariableVector variables_type = free_variables(type);
   VariableVector variables_body = free_variables(body);
   SubstLst subses
      = create_subst_lst(
         merge_variable_vectors(variables_type, variables_body));
   Term subst_type = type.ptr->subst_lst(subses);
   Term subst_body = body.ptr->subst_lst(subses);
   check_for_definition(subst_type, subst_body);
   add(Identifier(modules.top_level_module(), name), subst_type, subst_body);
}

void Environment::pop()
{
   definitions.pop_back();
}

Term Environment::type_of(const Name &name) const
{
   return lookup_iterator(name, true, true)->type;
}

Term Environment::look_up(const Name &name) const
{
   return lookup_iterator(name, true, true)->value;
}

bool Environment::has_name(HString name) const
{
   for (Definitions::const_reference p: definitions)
      if (p.name == name)
         return true;
   return false;
}

VariableVector Environment::get_globals() const
{
   VariableVector result;
   for (Definitions::const_reverse_iterator it = definitions.rbegin();
         it != definitions.rend(); ++it)
   {
      if (it->name.module_name != hstring_empty)
         break;
      result.push_back(it->name.name);
   }
   std::sort(result.begin(), result.end());
   return result;
}

bool find_string_in_string_vector(const std::vector<std::string> &vec,
                                  const std::string &find)
{
   return std::find(vec.begin(), vec.end(), find) != vec.end();
}

Environment::Definitions::const_reverse_iterator Environment::lookup_iterator(
        const Name &name, bool throw_on_not_found, bool add_module_name) const
{
   HString current_module;
   bool module_is_a_direct_import;
   bool module_is_an_indirect_import;
   bool can_use_module;
   for (Definitions::const_reverse_iterator it = definitions.rbegin();
         it != definitions.rend(); ++it)
   {
      HString module_name = it->name.module_name;
      if (module_name != current_module)
      {
         current_module = module_name;
         module_is_a_direct_import
            = modules.top_level_module() == module_name
            || modules.is_a_direct_import(module_name);
         module_is_an_indirect_import = false;
         if (!module_is_a_direct_import)
            module_is_an_indirect_import
               = modules.is_an_indirect_import(module_name);
         can_use_module
            = name.module_name == module_name
               || module_is_a_direct_import
               || (module_is_an_indirect_import
                   && name.module_name != hstring_empty);
      }
      // module cannot be used because it is not imported/called properly
      if (!can_use_module)
         continue;
      bool try_without_module = add_module_name && module_is_a_direct_import;
      if (it->name.name == name.name
            && ((try_without_module && name.module_name == hstring_empty)
                || it->name.module_name == name.module_name))
      {
         return it;
      }
   }
   if (throw_on_not_found)
      throw std::runtime_error("Identifier " + name.name.to_string()
                               + " was not declared");
   return definitions.rend();
}

SubstLst Environment::create_subst_lst(const VariableVector &variables)
{
   SubstLst subses;
   subses.reserve(variables.size());
   for (HString var: variables)
   {
      const Name &name = lookup_iterator(var, true, true)->name;
      subses.emplace_back(var, Identifier(name.module_name, name.name));
   }
   return subses;
}

void Environment::add(const Name &name, const Term &type,
                      const Term &value)
{
   if (lookup_iterator(name, false, false) != definitions.rend())
      throw std::runtime_error("Identifier " + name.name.to_string()
                               + " was already declared");
   definitions.emplace_back(name, type, value);
}

void Environment::check_for_axiom(HString name, const Term &type)
{
   Term type_of_type = normalize(*this, ::type_of(*this, type));
   if (!type_of_type.is_a_sort())
      ThrowRuntimeError()
         << "Identifier " << name << " is of type " << type_of_type
         << " which should be a sort";
}

void Environment::check_for_definition(const Term &type, const Term &body)
{
   Term type_of_body = ::type_of(*this, body);
   if (!red_compare(*this, type_of_body, type, CompareKind::LE))
      ThrowRuntimeError()
         << "type of body is " << type_of_body << " but was declared to be "
         << type;
}

/********************
 * type_of function *
 ********************/

Term type_of(Environment &e, const Term &t)
{
   return t.ptr->type_of(e);
}

/***************************
 * free_variables function *
 ***************************/

VariableVector free_variables(const Term &t)
{
   return t.ptr->free_variables();
}

/*****************************
 * add_to_variables function *
 *****************************/

void add_to_variables(VariableVector &v, HString name)
{
    auto it = equal_range(v.begin(), v.end(), name);
    if (it.first == it.second)
        v.insert(it.first, name);
}

/***********************************
 * merge_variable_vectors function *
 ***********************************/

VariableVector merge_variable_vectors(const VariableVector &v1,
                                      const VariableVector &v2)
{
   VariableVector result(v1.size() + v2.size());
   merge(v1.begin(), v1.end(), v2.begin(), v2.end(), result.begin());
   VariableVector::iterator end = std::unique(result.begin(), result.end());
   result.erase(end, result.end());
   return result;
}

/*************************
 * new_variable function *
 *************************/

HString new_variable(HString var, const VariableVector& in_use)
{
   if (find(in_use.begin(), in_use.end(), var) == in_use.end())
      return var;
   std::pair<HString, int> p = split_base_number(var);
   while (true)
   {
      std::string new_var = p.first.to_string() + std::to_string(p.second);
      HString h_new_var(new_var.c_str());
      if (find(in_use.begin(), in_use.end(), h_new_var) == in_use.end())
         return h_new_var;
      ++p.second;
   }
}

/**********************
 * normalize function *
 **********************/

Term normalize(Environment &e, const Term &t)
{
   std::shared_ptr<const Basic> result = t.ptr;
   while (true)
   {
      std::shared_ptr<const Basic> normalized = result->normalize(e).ptr;
      if (normalized == result)
         return result;
      result = normalized;
   }
}

/************************
 * red_compare function *
 ************************/

bool red_compare(Environment &e, const Term &t1, const Term &t2, CompareKind kind)
{
   if (t1 == t2)
   {
      if (kind == CompareKind::LE)
         e.universes.add_lt(dynamic_cast<const Type*>(t1.ptr.get()),
                            dynamic_cast<const Type*>(t2.ptr.get()));
      return true;
   }
   if (t1.is_a<Identifier>())
   {
      Term result = e.look_up(*(Identifier*)t1.ptr.get());
      if (result.ptr != t1.ptr)
         return red_compare(e, result, t2, kind);
   }
   if (t2.is_a<Identifier>())
   {
      Term result = e.look_up(*(Identifier*)t2.ptr.get());
      if (result.ptr != t2.ptr)
         return red_compare(e, t1, result, kind);
   }
   if (t1.is_a<Apply>())
   {
      Term result = head_reduce(e, t1).ptr;
      if (result.ptr != t1.ptr)
         return red_compare(e, result, t2, kind);
   }
   if (t2.is_a<Apply>())
   {
      Term result = head_reduce(e, t2).ptr;
      if (result.ptr != t2.ptr)
         return red_compare(e, t1, result, kind);
   }
   if (kind == CompareKind::LE && t2.is_a<Type>())
   {
      if (t1.is_a<Prop>())
         return true;
      if (t1.is_a<TypeSucc>())
      {
          e.universes.add_lt(
             dynamic_cast<const Type*>(((const TypeSucc*)t1.ptr.get())->arg.ptr.get()),
             (const Type*)t2.ptr.get());
          return true;
      }
      if (t1.is_a<TypeMax>())
      {
         const TypeMax *type_max = (const TypeMax*)(t1.ptr.get());
         return red_compare(e, type_max->arg1, t2, CompareKind::LE)
             && red_compare(e, type_max->arg2, t2, CompareKind::LE);
      }
   }
   if (t1.get_term_type() == t2.get_term_type())
      return t1.ptr->red_compare(e, *t2.ptr.get(), kind);
   return false;
}

