#include "token.h"
#include "system.h"
#include <functional>
#include <ostream>

enum struct Associativity { none, left, right };

class ParseRule
{
public:
   template <class... Args>
   ParseRule(Args&&... args...):
      tokens { make_shared_token(std::move(args))... } {}
   virtual std::pair<int, int> get_priority() const = 0;
   void print(int pos, std::ostream &os) const;
   void reserve_sizes(ParseResult &result) const;
   bool matches(int pos, const Token &tok) const;
   void process(int pos, const Token &tok, ParseResult &result) const;
   size_t size() const;
private:
   std::vector<std::shared_ptr<Token>> tokens;
};

class ParseTermRule: public ParseRule
{
public:
   typedef std::function<Term(const ParseResult&)> CreateTerm;
   template <class... Args>
   ParseTermRule(Args&&... args...):
      ParseRule(std::move(args)...),
      continue_matching(false),
      priority(1000, 0),
      associativity(Associativity::none) {}
   bool get_continue_matching() const;
   void set_continue_matching();
   std::pair<int, int> get_priority() const override;
   void set_priority(int priority);
   Associativity get_associativity() const;
   void set_associativity(Associativity a);
   void set_function(CreateTerm&& create_term_);
   Term get_parse_result(const ParseResult &result) const;
private:
   CreateTerm create_term;
   bool continue_matching;
   std::pair<int, int> priority; // (ext, int) priority
   Associativity associativity;
};

class ParseCommandRule: public ParseRule
{
public:
   typedef std::function<void(const ParseResult &result)> ProcessResult;
   template <class... Args>
   ParseCommandRule(Args&&... args...): ParseRule(std::move(args)...){}
   std::pair<int, int> get_priority() const override;
   void set_function(ProcessResult&& process_result_function);
   void process_result(const ParseResult &result) const;
private:
   ProcessResult process_result_function;
};

