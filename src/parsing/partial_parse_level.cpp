#include "partial_parse_level.h"

/*****************************
 * PartialParseLevel methods *
 *****************************/

PartialParseLevel::PartialParseLevel(): pos(0) {}

PartialParseLevel::PartialParseLevel(int pos, const ParseResult &result):
   pos(pos), result(result) {}

void PartialParseLevel::print(std::ostream &os) const
{
   get_rule()->print(pos, os);
}

bool PartialParseLevel::matches(const Token &tok) const
{
   return get_rule()->matches(pos, tok);
}

bool PartialParseLevel::is_complete() const
{
   return pos == get_rule()->size();
}

void PartialParseLevel::process(const Token &tok)
{
   get_rule()->process(pos, tok, result);
   ++pos;
}

void PartialParseLevel::process(Term &t)
{
   result.terms.push_back(t);
   ++pos;
}

/*********************************
 * PartialParseLevelTerm methods *
 *********************************/

PartialParseLevelTerm::PartialParseLevelTerm(
   std::shared_ptr<const ParseTermRule> rule): rule(rule)
{
   get_rule()->reserve_sizes(result);
}

PartialParseLevelTerm::PartialParseLevelTerm(int pos,
      const ParseResult &result, std::shared_ptr<const ParseTermRule> rule):
   PartialParseLevel(pos, result), rule(rule) {}

std::shared_ptr<PartialParseLevel> PartialParseLevelTerm::clone() const
{
   return std::make_shared<PartialParseLevelTerm>(pos, result, rule);
}

std::shared_ptr<const ParseRule> PartialParseLevelTerm::get_rule() const
{
   return rule;
}

Term PartialParseLevelTerm::get_finished_parse_result() const
{
   if (pos != rule->size())
      return Term();
   return rule->get_parse_result(result);
}

/************************************
 * PartialParseLevelCommand methods *
 ************************************/

PartialParseLevelCommand::PartialParseLevelCommand(
      std::shared_ptr<const ParseCommandRule> rule):
   rule(rule) {}

PartialParseLevelCommand::PartialParseLevelCommand(int pos,
      const ParseResult &result, std::shared_ptr<const ParseCommandRule> rule):
   PartialParseLevel(pos, result), rule(rule) {}

std::shared_ptr<PartialParseLevel> PartialParseLevelCommand::clone() const
{
   return std::make_shared<PartialParseLevelCommand>(pos, result, rule);
}

std::shared_ptr<const ParseRule> PartialParseLevelCommand::get_rule() const
{
   return rule;
}

void PartialParseLevelCommand::process_completed()
{
   rule->process_result(result);
}

