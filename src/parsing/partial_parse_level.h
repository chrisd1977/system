#include <memory>
#include "parse_rule.h"

class PartialParseLevel
{
public:
   PartialParseLevel();
   PartialParseLevel(int pos, const ParseResult &result);
   virtual ~PartialParseLevel() = default;
   virtual std::shared_ptr<PartialParseLevel> clone() const = 0;
   void print(std::ostream &os) const;
   virtual std::shared_ptr<const ParseRule> get_rule() const = 0;
   bool matches(const Token &tok) const;
   bool is_complete() const;
   void process(const Token &tok);
   void process(Term &t);
protected:
   int pos;
   ParseResult result;
};

class PartialParseLevelTerm: public PartialParseLevel
{
public:
   PartialParseLevelTerm(std::shared_ptr<const ParseTermRule> rule);
   PartialParseLevelTerm(int pos, const ParseResult &result,
                         std::shared_ptr<const ParseTermRule> rule);
   std::shared_ptr<PartialParseLevel> clone() const override;
   std::shared_ptr<const ParseRule> get_rule() const override;
   Term get_finished_parse_result() const;
private:
   std::shared_ptr<const ParseTermRule> rule;
};

class PartialParseLevelCommand: public PartialParseLevel
{
public:
   PartialParseLevelCommand(std::shared_ptr<const ParseCommandRule> rule);
   PartialParseLevelCommand(int pos, const ParseResult &result,
                            std::shared_ptr<const ParseCommandRule> rule);
   std::shared_ptr<PartialParseLevel> clone() const override;
   std::shared_ptr<const ParseRule> get_rule() const override;
   void process_completed();
private:
   std::shared_ptr<const ParseCommandRule> rule;
};

