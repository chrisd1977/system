#include "partial_parse.h"
#include "util.h"

class Parser
{
public:
   Parser();
protected:
   void parse_loop(ParseContext ctxt);
   void remove_opt_spacers();
   void process_token(std::shared_ptr<Token> tok);
   bool opt_spacers_present() const;
   bool completed_parses_present() const;
   void process_completed_parses();
   virtual bool maybe_finish_parse(std::streambuf &buf) = 0;
   std::shared_ptr<PartialParse> get_complete_parse();
protected:
   std::vector<std::shared_ptr<ParseTermRule>> rules;
   std::vector<std::shared_ptr<PartialParse>> parses;
};

class TermParser: public Parser
{
public:
   Term parse(ParseContext ctxt);
private:
   bool maybe_finish_parse(std::streambuf &buf) override;
   void try_to_finish_parse();
private:
   std::shared_ptr<const Basic> result;
};

class CommandParser: public Parser
{
public:
   CommandParser(Environment &e, std::vector<std::string> path);
   void parse(ParseContext ctxt);
private:
   bool maybe_finish_parse(std::streambuf &buf) override;
private:
   std::vector<std::shared_ptr<ParseCommandRule>> command_rules;
};

void parse_streambuf(
    std::streambuf &buf, const std::string &file_name, CommandParser &parser);

