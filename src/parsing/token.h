#pragma once
#include "system.h"
#include "hstring.h"

struct ParseResult
{
   std::vector<Term> terms;
   std::vector<HString> words;
};

class Token
{
public:
   virtual void print(std::ostream &os) const;
   virtual bool matches(const Token &other) const;
   virtual bool matches_same_type(const Token &other) const;
   virtual void process(const Token &other, ParseResult &result) const;
};

class OptSpacer: public Token
{
   virtual void print(std::ostream &os) const;
};

class Char: public Token
{
public:
   Char(char c);
   void print(std::ostream &os) const override;
   bool matches_same_type(const Token &other) const override;
private:
   char c;
};

class Word: public Token
{
public:
   Word(HString word);
   void print(std::ostream &os) const override;
   bool matches_same_type(const Token &other) const override;
public:
   HString word;
};

class AnyWord: public Token
{
   void print(std::ostream &os) const override;
   bool matches(const Token &other) const override;
   void process(const Token &other, ParseResult &result) const override;
};

class TermToken: public Token
{
   void print(std::ostream &os) const override;
};

template <class T>
std::shared_ptr<Token> make_shared_token(T&& arg)
{
   return std::make_shared<T>(std::move(arg));
}

std::ostream &operator<<(std::ostream &os, const Token &tok);

