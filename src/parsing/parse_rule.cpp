#include "parse_rule.h"

/*********************
 * ParseRule methods *
 *********************/

void ParseRule::print(int pos, std::ostream &os) const
{
   os << "{ ";
   for (int i = 0; i < tokens.size(); ++i)
   {
      if (i)
         os << ", ";
      if (i == pos)
         os << "*";
      tokens[i]->print(os);
   }
   os << " }";
}

void ParseRule::reserve_sizes(ParseResult &result) const
{
   int num_terms = 0, num_words = 0;
   for (std::shared_ptr<Token> tok: tokens)
   {
      if (typeid(*tok) == typeid(AnyWord))
         ++num_words;
      else if (typeid(*tok) == typeid(TermToken))
         ++num_terms;
      result.words.reserve(num_words);
      result.terms.reserve(num_terms);
   }
}

bool ParseRule::matches(int pos, const Token &tok) const
{
   return tokens[pos]->matches(tok);
}

void ParseRule::process(int pos, const Token &tok, ParseResult &result) const
{
   tokens[pos]->process(tok, result);
}

size_t ParseRule::size() const
{
   return tokens.size();
}

std::ostream &operator<<(std::ostream &os, const ParseRule &rule)
{
   rule.print(-1, os);
   return os;
}

/*************************
 * ParseTermRule methods *
 *************************/

bool ParseTermRule::get_continue_matching() const
{
    return continue_matching;
}

void ParseTermRule::set_continue_matching()
{
    continue_matching = true;
}

std::pair<int, int> ParseTermRule::get_priority() const
{
   return priority;
}

void ParseTermRule::set_priority(int priority)
{
   this->priority.first = priority;
   this->priority.second = priority;
}

Associativity ParseTermRule::get_associativity() const
{
   return associativity;
}

void ParseTermRule::set_associativity(Associativity a)
{
   associativity = a;
}

void ParseTermRule::set_function(CreateTerm&& create_term_)
{
   create_term = std::move(create_term_);
}

Term ParseTermRule::get_parse_result(const ParseResult &result) const
{
   return create_term(result);
}

/****************************
 * ParseCommandRule methods *
 ****************************/

std::pair<int, int> ParseCommandRule::get_priority() const
{
   return std::make_pair(0, 0);
}

void ParseCommandRule::set_function(ProcessResult&& create_result)
{
   process_result_function = std::move(create_result);
}

void ParseCommandRule::process_result(const ParseResult &result) const
{
   process_result_function(result);
}

