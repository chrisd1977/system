#include "util.h"
#include "throw_runtime_error.h"
#include <cstring>

void parse_character(std::streambuf &buf, char c)
{
   if (buf.sbumpc() != c)
      ThrowRuntimeError() << "a " << c << " was expected but not found";
}

bool is_space_character(int c)
{
   return c == ' ' || c == '\t' || c == '\r' || c == '\n' || c =='#';
}

bool is_end_of_line_character(int c)
{
   return c == '\n' || c == '\r' || c == EOF;
}

bool is_allowed_first_char(int c)
{
   return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' ||  c == '_';
}

bool is_allowed_char(int c)
{
   return is_allowed_first_char(c) || c == '\'' || c >= '0' && c <= '9';
}

void parse_spaces(ParseContext ctxt)
{
   int c = ctxt.buf.sgetc();
   while (true)
   {
      if (c == '#')
         while (!is_end_of_line_character(c))
            c = ctxt.buf.snextc();
      if (c == '\n')
        ++ctxt.line_number;
      if (!is_space_character(c))
         return;
      c = ctxt.buf.snextc();
   }
}

HString get_name(ParseContext ctxt)
{
   static std::string result;
   int c = ctxt.buf.sbumpc();
   if (!is_allowed_first_char(c))
      ThrowRuntimeError() << "unexpected character: " << char(c);
   result.clear();
   result.push_back(c);
   while (true)
   {
      c = ctxt.buf.sgetc();
      if (!is_allowed_char(c))
         break;
      result.push_back(c);
      ctxt.buf.sbumpc();
   }
   parse_spaces(ctxt);
   return HString(result.c_str());
}

std::shared_ptr<Token> get_token(ParseContext ctxt)
{
   int c = ctxt.buf.sgetc();
   if (is_space_character(c))
   {
      parse_spaces(ctxt);
      return std::make_shared<OptSpacer>();
   }
   if (!is_allowed_char(c))
   {
      ctxt.buf.sbumpc();
      return std::make_shared<Char>(c);
   }
   HString name = get_name(ctxt);
   return std::make_shared<Word>(name);
}

