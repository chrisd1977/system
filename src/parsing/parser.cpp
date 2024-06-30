#include "parser.h"
#include "token.h"
#include "throw_runtime_error.h"
#include "basic.h"
#include <ostream>
#include <fstream>
#include <filesystem>

void check_name(HString name)
{
   if (name == hstring_underscore)
      throw std::runtime_error("The name '_' is not allowed to be assummed "
                               "or defined.");
}

/******************
 * Parser methods *
 ******************/

Parser::Parser()
{
   rules =
   {
      std::make_shared<ParseTermRule>(Char('('), OptSpacer(), TermToken(),
         Char(')'), OptSpacer()),
      std::make_shared<ParseTermRule>(Word(hstring_forall), AnyWord(),
         Char(':'), OptSpacer(), TermToken(), Char(','), OptSpacer(),
         TermToken()),
      std::make_shared<ParseTermRule>(Word(hstring_lambda), AnyWord(),
         Char(':'), OptSpacer(), TermToken(), Char(','), OptSpacer(),
         TermToken()),
      std::make_shared<ParseTermRule>(Word(hstring_Prop)),
      std::make_shared<ParseTermRule>(Word(hstring_Type)),
      std::make_shared<ParseTermRule>(AnyWord()),
      std::make_shared<ParseTermRule>(AnyWord(), Char('.'), AnyWord()),
      std::make_shared<ParseTermRule>(TermToken(), TermToken()),
      std::make_shared<ParseTermRule>(TermToken(), Char('-'), Char('>'),
         OptSpacer(), TermToken())
   };
   rules[0]->set_function(
      [](const ParseResult &result) -> Term
      {
         return result.terms[0];
      });
   rules[1]->set_function(
      [](const ParseResult &result) -> Term
      {
         return Term(std::make_shared<Forall>(result.words[0], result.terms[0],
                                              result.terms[1]));
      });
   rules[2]->set_function(
      [](const ParseResult &result) -> Term
      {
         return Term(std::make_shared<Lambda>(result.words[0], result.terms[0],
                                              result.terms[1]));
      });
   rules[3]->set_function(
      [](const ParseResult &result) -> Term
      {
         return Term(std::make_shared<Prop>());
      });
   rules[4]->set_function(
      [](const ParseResult &result) -> Term
      {
         return Term(std::make_shared<Type>());
      });
   rules[5]->set_function(
      [](const ParseResult &result) -> Term
      {
         if (result.words[0] == hstring_underscore)
            ThrowRuntimeError() << "_ is not allowed as an identifier";
         return Term(std::make_shared<Identifier>(result.words[0]));
      });
   rules[6]->set_function(
      [](const ParseResult &result) -> Term
      {
         return Term(
            std::make_shared<Identifier>(result.words[0], result.words[1]));
      });
   rules[7]->set_function(
      [](const ParseResult &result) -> Term
      {
         return Term(std::make_shared<Apply>(result.terms[0], result.terms[1]));
      });
   rules[8]->set_function(
      [](const ParseResult &result) -> Term
      {
         return Term(std::make_shared<Forall>(
            hstring_underscore, result.terms[0], result.terms[1]));
      });
   rules[1]->set_priority(5);         // Forall
   rules[2]->set_priority(5);         // Lambda
   rules[5]->set_continue_matching(); // Identifier
   rules[7]->set_priority(500);       // Apply
   rules[7]->set_associativity(Associativity::left); // Apply
   rules[8]->set_priority(200);       // _ -> _
   rules[8]->set_associativity(Associativity::right); // _ -> _
}

void Parser::parse_loop(ParseContext ctxt)
{
   while (true)
   {
      std::shared_ptr<Token> tok = get_token(ctxt);
      process_token(tok);
      bool has_space = is_space_character(ctxt.buf.sgetc());
      while (!has_space && opt_spacers_present() || completed_parses_present())
      {
         if (!has_space)
            remove_opt_spacers();
         process_completed_parses();
      }
      if (maybe_finish_parse(ctxt.buf))
         return;
   }
}

void Parser::remove_opt_spacers()
{
   for (std::shared_ptr<PartialParse> &pp: parses)
      if (pp->matches(OptSpacer()))
         pp->process(OptSpacer());
}

void Parser::process_token(std::shared_ptr<Token> tok)
{
   std::vector<std::shared_ptr<PartialParse>> new_parses;
   for (std::shared_ptr<PartialParse> pp: parses)
   {
      if (pp->parse_is_complete())
         continue;
      if (pp->matches(TermToken()))
      {
         for (std::shared_ptr<ParseTermRule> pr: rules)
         {
            if (pr->matches(0, *tok))
            {
               if (pr->get_continue_matching())
                  new_parses.push_back(pp->clone());
               else
                  new_parses.push_back(pp);
               new_parses.back()->add_rule(pr);
               new_parses.back()->process(*tok);
               if (!pr->get_continue_matching())
                  break;
            }
         }
      }
      else if (pp->matches(*tok))
      {
         new_parses.push_back(pp);
         new_parses.back()->process(*tok);
      }
   }
   parses = std::move(new_parses);
   if (parses.empty())
      ThrowRuntimeError() << "unexpected token " << *tok;
}

bool Parser::opt_spacers_present() const
{
   for (std::shared_ptr<PartialParse> pp: parses)
      if (pp->matches(OptSpacer()))
         return true;
   return false;
}

bool Parser::completed_parses_present() const
{
   for (std::shared_ptr<PartialParse> parse: parses)
      if (parse->toplevel_is_complete())
         return true;
   return false;
}

void Parser::process_completed_parses()
{
   std::vector<std::shared_ptr<PartialParse>> new_parses;
   for (std::shared_ptr<PartialParse> pp: parses)
   {
      if (pp->toplevel_is_complete())
      {
         std::shared_ptr<const ParseRule> prev_toplevel_rule
            = pp->get_toplevel_rule();
         std::pair<int, int> priority = pp->get_toplevel_rule()->get_priority();
         Term t = pp->pop_off_toplevel_term();
         for (std::shared_ptr<ParseTermRule> pr: rules)
            if (pr->matches(0, TermToken()))
            {
               if (pr->get_priority().second > priority.first)
                  continue;
               if (pp->get_toplevel_rule()->get_priority().second
                     > pr->get_priority().first)
                  continue;
               if (pr == pp->get_toplevel_rule()
                     && pr->get_associativity() == Associativity::left)
                  continue;
               if (pr == prev_toplevel_rule
                     && pr->get_associativity() == Associativity::right)
                  continue;
               new_parses.push_back(pp->clone());
               new_parses.back()->add_rule(pr);
               new_parses.back()->process(t);
            }
         new_parses.push_back(pp);
         new_parses.back()->process(t);
      }
      else
      {
         new_parses.push_back(pp);
      }
   }
   parses = std::move(new_parses);
}

std::shared_ptr<PartialParse> Parser::get_complete_parse()
{
   std::shared_ptr<PartialParse> completed;
   for (std::shared_ptr<PartialParse> pp: parses)
   {
      bool is_complete = pp->parse_is_complete();
      if (!is_complete)
         continue;
      if (completed)
         ThrowRuntimeError() << "ambiguous parse";
      completed = pp;
   }
   return completed;
}

/**********************
 * TermParser methods *
 **********************/

Term TermParser::parse(ParseContext ctxt)
{
   parses.push_back(std::make_shared<PartialParseTerm>());
   parse_loop(ctxt);
   return result;
}

bool TermParser::maybe_finish_parse(std::streambuf &buf)
{
   int c = buf.sgetc();
   if (c == ':' || c == '.' || c == EOF)
   {
      try_to_finish_parse();
      return !!result;
   }
   return false;
}

void TermParser::try_to_finish_parse()
{
   std::shared_ptr<PartialParse> completed = get_complete_parse();
   if (completed)
      result = std::static_pointer_cast<PartialParseTerm>(completed)
                                            ->get_finished_parse_result().ptr;
}

/*****************
 * CommandParser *
 *****************/

CommandParser::CommandParser(Environment &e, std::vector<std::string> path)
{
   command_rules =
   {
      std::make_shared<ParseCommandRule>(Word(hstring_Axiom), AnyWord(),
         Char(':'), OptSpacer(), TermToken(), Char('.')),
      std::make_shared<ParseCommandRule>(Word(hstring_Definition), AnyWord(),
         Char(':'), OptSpacer(), TermToken(), Char(':'), Char('='), OptSpacer(),
         TermToken(), Char('.')),
      std::make_shared<ParseCommandRule>(Word(hstring_Require), AnyWord(),
         Char('.'))
   };
   command_rules[0]->set_function(
      [&e](const ParseResult &result)
      {
         check_name(result.words[0]);
         e.axiom(result.words[0], result.terms[0]);
      });
   command_rules[1]->set_function(
      [&e](const ParseResult &result)
      {
         check_name(result.words[0]);
         e.definition(result.words[0], result.terms[0], result.terms[1]);
      });
   command_rules[2]->set_function(
      [this, &e, path{std::move(path)}](const ParseResult &result)
      {
         if (e.modules.import_module(result.words[0]))
            return;
         std::filebuf buf;
         std::string file = result.words[0].append_to_string(".s");
         for (const std::string &dir: path)
            if (buf.open(std::filesystem::path(dir) / file, std::ios_base::in))
            {
               e.modules.push_module(result.words[0]);
               parse_streambuf(buf, file, *this);
               e.modules.pop_module();
               return;
            }
         std::string exception_text =
            "could not open module " + result.words[0].to_string()
               + ", looking in directories ";
         for (const std::string &dir: path)
            exception_text += dir + ", ";
         exception_text.resize(exception_text.size() - 2);
         throw std::runtime_error(exception_text);
      });
}

void CommandParser::parse(ParseContext ctxt)
{
   parses.clear();
   for (std::shared_ptr<ParseCommandRule> r: command_rules)
      parses.push_back(std::make_shared<PartialParseCommand>(r));
   parse_loop(ctxt);
}

bool CommandParser::maybe_finish_parse(std::streambuf &buf)
{
   std::shared_ptr<PartialParse> completed = get_complete_parse();
   if (!completed)
      return false;
   std::static_pointer_cast<PartialParseCommand>(completed)
                                                     ->process_parse_result();
   return true;
}

class ParseError: public std::runtime_error
{
public:
    ParseError(const std::string &msg): runtime_error(msg) {}
};

void parse_streambuf(std::streambuf &buf, const std::string &file_name,
                     CommandParser &parser)
{
   int initial_line_number = 1, line_number = 1;
   try
   {
      while (true)
      {
         parse_spaces({ buf, initial_line_number });
         if (buf.sgetc() == EOF)
            return;
         line_number = initial_line_number;
         parser.parse({ buf, line_number });
         initial_line_number = line_number;
      }
   }
   catch (ParseError&)
   {
      throw;
   }
   catch (std::runtime_error &e)
   {
      std::ostringstream os;
      os << file_name << ":" << initial_line_number << ": " << e.what();
      throw ParseError(os.str());
   }
}

