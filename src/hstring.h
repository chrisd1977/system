#pragma once
#include <cstddef>
#include <vector>
#include <ostream>

class HString
{
friend std::pair<HString, int> split_base_number(HString s);
public:
   HString();
   HString(const char *s);
   void print(std::ostream &os) const;
   bool empty() const;
   bool operator==(HString other) const
   {
      return value == other.value;
   }
   bool operator!=(HString other) const
   {
      return value != other.value;
   }
   bool operator<(HString other) const
   {
      return value < other.value;
   }
   std::string to_string() const;
   std::string append_to_string(const char *append) const;
private:
   const char *value;
};

std::ostream &operator<<(std::ostream &os, HString s);

std::pair<HString, int> split_base_number(HString s);

extern HString hstring_empty;
extern HString hstring_underscore;
extern HString hstring_forall;
extern HString hstring_lambda;
extern HString hstring_Prop;
extern HString hstring_Type;
extern HString hstring_Axiom;
extern HString hstring_Definition;
extern HString hstring_Require;

