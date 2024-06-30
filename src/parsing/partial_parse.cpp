#include "partial_parse.h"

/************************
 * PartialParse methods *
 ************************/

PartialParse::PartialParse(const PartialParse &other)
{
   parse_stack.reserve(other.parse_stack.size());
   for (std::shared_ptr<PartialParseLevel> level: other.parse_stack)
      parse_stack.push_back(level->clone());
}

void PartialParse::copy_stack(const ParseStack &stack)
{
   for (std::shared_ptr<PartialParseLevel> lev: stack)
      parse_stack.push_back(lev->clone());
}

void PartialParse::print(std::ostream &os) const
{
   for (std::shared_ptr<const PartialParseLevel> lev: parse_stack)
   {
      lev->print(os);
      os << std::endl;
   }
}

int PartialParse::size() const
{
   return parse_stack.size();
}

std::shared_ptr<const ParseRule> PartialParse::get_toplevel_rule() const
{
   return parse_stack.back()->get_rule();
}

void PartialParse::add_rule(std::shared_ptr<ParseTermRule> rule)
{
   parse_stack.push_back(std::make_shared<PartialParseLevelTerm>(rule));
}

bool PartialParse::matches(const Token &tok) const
{
   if (parse_stack.back()->is_complete())
      return false;
   return parse_stack.back()->matches(tok);
}

bool PartialParse::toplevel_is_complete() const
{
   return parse_stack.back()->is_complete() && parse_stack.size() != 1;
}

void PartialParse::process(const Token &tok)
{
   parse_stack.back()->process(tok);
}

void PartialParse::process(Term &t)
{
   parse_stack.back()->process(t);
}

bool PartialParse::parse_is_complete() const
{
   return parse_stack.size() == 1 && parse_stack.back()->is_complete();
}


Term PartialParse::pop_off_toplevel_term()
{
   Term result = ((PartialParseLevelTerm&)(*parse_stack.back()))
                                                .get_finished_parse_result();
   parse_stack.pop_back();
   return result;
}

std::ostream &operator<<(std::ostream &os, const PartialParse &pp)
{
   pp.print(os);
   return os;
}

/****************************
 * PartialParseTerm methods *
 ****************************/

PartialParseTerm::PartialParseTerm(bool add_default_rule)
{
   parse_stack.reserve(10);
   if (!add_default_rule)
      return;
   static std::shared_ptr<ParseTermRule> rule;
   if (!rule)
   {
      rule = std::make_shared<ParseTermRule>(TermToken());
      rule->set_function(
         [](const ParseResult &result)
         {
            return result.terms[0];
         });
   }
   add_rule(rule);
}

std::shared_ptr<PartialParse> PartialParseTerm::clone() const
{
   auto result = std::make_shared<PartialParseTerm>(false);
   result->copy_stack(this->parse_stack);
   return result;
}

Term PartialParseTerm::get_finished_parse_result() const
{
   return ((PartialParseLevelTerm&)(*parse_stack.back()))
                                             .get_finished_parse_result().ptr;
}

/*******************************
 * PartialParseCommand methods *
 *******************************/

PartialParseCommand::PartialParseCommand(
      std::shared_ptr<const ParseCommandRule> rule)
{
   parse_stack.reserve(10);
   if (rule)
      parse_stack.push_back(std::make_shared<PartialParseLevelCommand>(rule));
}

std::shared_ptr<PartialParse> PartialParseCommand::clone() const
{
   auto result = std::make_shared<PartialParseCommand>();
   result->copy_stack(this->parse_stack);
   return result;
}

void PartialParseCommand::process_parse_result()
{
   std::static_pointer_cast<PartialParseLevelCommand>(parse_stack.back())
      ->process_completed();
}

