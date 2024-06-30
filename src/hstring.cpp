#include "hstring.h"
#include <cstring>
#include <cstdlib>

namespace {

class HashTable
{
public:
   HashTable();
   size_t calculate_hash(const char *s, size_t size);
   const char *get_or_create_string(const char *s, size_t idx, size_t size);
private:
   void resize();
   void reinsert_string(char *s, size_t idx, size_t size);
private:
   int num_bits;
   size_t num_strings;
   size_t max_num_strings;
   std::vector<char*> hash_table;
} hash_table;


HashTable::HashTable(): num_bits(10), num_strings(0)
{
   resize();
}

size_t HashTable::calculate_hash(const char *s, size_t size)
{
   size_t num_octets = size / 8;
   size_t data;
   size_t result = 0;
   for (int i = 0; i < num_octets; ++i)
   {
      memcpy(&data, s + 8 * i, 8);
      result += 11400714819323198485llu * data;
   }
   size_t rest = size - 8 * num_octets;
   if (rest)
   {
      memcpy(&data, s + 8 * num_octets, rest);
      memset(((char*)&data) + rest, 0, 8 - rest);
      result += 11400714819323198485llu * data;
   }
   result >>= (64 - num_bits);
   return result;
}

const char *HashTable::get_or_create_string(
      const char *s, size_t idx, size_t size)
{
   while (hash_table[idx] && strcmp(s, hash_table[idx]))
      ++idx;
   if (idx >> num_bits)
   {
      idx = 0;
      while (hash_table[idx] && strcmp(s, hash_table[idx]))
         ++idx;
   }
   if (!hash_table[idx])
   {
      ++num_strings;
      if (num_strings > max_num_strings)
      {
         std::vector<char*> copy = std::move(hash_table);
         resize();
         for (char *val: copy)
         {
            size_t size = strlen(val);
            size_t idx = calculate_hash(val, size);
            reinsert_string(val, idx, size);
         }
         return get_or_create_string(s, calculate_hash(s, size), size);
      }
      hash_table[idx] = new char[size+1];
      strcpy(hash_table[idx], s);
   }
   return hash_table[idx];
}

void HashTable::resize()
{
   ++num_bits;
   max_num_strings = (1 << (num_bits + 1))/3;
   hash_table.resize((1 << num_bits) + 1);
}

void HashTable::reinsert_string(char *s, size_t idx, size_t size)
{
   while (hash_table[idx])
      ++idx;
   if (idx >> num_bits)
   {
      idx = 0;
      while (hash_table[idx])
         ++idx;
   }
   hash_table[idx] = s;
}

}

HString::HString(): value(nullptr) {}

HString::HString(const char *s)
{
   size_t size = strlen(s);
   size_t idx = hash_table.calculate_hash(s, size);
   value = hash_table.get_or_create_string(s, idx, size);
}

void HString::print(std::ostream &os) const
{
   os << value;
}

bool HString::empty() const
{
    return !*value;
}

std::string HString::to_string() const
{
   return value;
}

std::string HString::append_to_string(const char *append) const
{
    std::string result;
    result.reserve(strlen(value) + strlen(append));
    result += value;
    result += append;
    return result;
}

std::ostream &operator<<(std::ostream &os, HString s)
{
    s.print(os);
    return os;
}

std::pair<HString, int> split_base_number(HString s)
{
    size_t len = strlen(s.value);
    const char *it = s.value + len - 1;
    for (; it >= s.value; --it)
        if (!isdigit(*it))
            break;
    std::string base = std::string(s.value, it + 1);
    return std::make_pair(HString(base.c_str()), atoi(it + 1));
}

HString hstring_empty("");
HString hstring_underscore("_");
HString hstring_forall("forall");
HString hstring_lambda("lambda");
HString hstring_Prop("Prop");
HString hstring_Type("Type");
HString hstring_Axiom("Axiom");
HString hstring_Definition("Definition");
HString hstring_Require("Require");

