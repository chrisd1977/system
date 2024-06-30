#include "parsing.h"
#include "parser.h"
#include "util.h"
#include "throw_runtime_error.h"

Term parse_term(std::streambuf &buf)
{
   int line_number = 1;
   parse_spaces({ buf, line_number });
   TermParser parser;
   return parser.parse({ buf, line_number });
}

Term parse(const std::string &s)
{
   std::stringbuf buf(s);
   Term t = parse_term(buf);
   if (buf.sgetc() != EOF)
      ThrowRuntimeError() << "unexpected character " << char(buf.sgetc())
                          << " after term";
   return t;
}

void parse_environment(std::streambuf &buf, Environment& e,
                       std::vector<std::string> path)
{
   CommandParser parser(e, path);
   parse_streambuf(buf, path.front(), parser);
}

