#include "token.h"
#include <ostream>

/*****************
 * Token methods *
 *****************/

void Token::print(std::ostream &os) const
{
   os << "<token>";
}

bool Token::matches(const Token &other) const
{
   if (typeid(*this) != typeid(other))
      return false;
   return matches_same_type(other);
}

bool Token::matches_same_type(const Token &other) const
{
   return true;
}

void Token::process(const Token &other, ParseResult &result) const {}

/*********************
 * OptSpacer methods *
 *********************/

void OptSpacer::print(std::ostream &os) const
{
   os << "<spacer>";
}

/****************
 * Char methods *
 ****************/

Char::Char(char c): c(c) {}

void Char::print(std::ostream &os) const
{
   os << '\'' << c << '\'';
}

bool Char::matches_same_type(const Token &other) const
{
   return c == ((const Char&)other).c;
}

/****************
 * Word methods *
 ****************/

Word::Word(HString word): word(word) {}

void Word::print(std::ostream &os) const
{
   os << '"' << word << '"';
}

bool Word::matches_same_type(const Token &other) const
{
   return word == ((const Word&)other).word;
}

/*******************
 * Anyword methods *
 *******************/

void AnyWord::print(std::ostream &os) const
{
   os << "<word>";
}

bool AnyWord::matches(const Token &other) const
{
   return typeid(other) == typeid(Word) || typeid(other) == typeid(AnyWord);
}

void AnyWord::process(const Token &other, ParseResult &result) const
{
   result.words.push_back(((const Word&)other).word);
}

/*********************
 * TermToken methods *
 *********************/

void TermToken::print(std::ostream &os) const
{
   os << "<term>";
}

/************************
 * operator<< for Token *
 ************************/

std::ostream &operator<<(std::ostream &os, const Token &tok)
{
   tok.print(os);
   return os;
}

