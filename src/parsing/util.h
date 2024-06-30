#pragma once
#include "token.h"
#include <memory>
#include <streambuf>

struct ParseContext
{
    std::streambuf &buf;
    int &line_number;
};

void parse_character(std::streambuf &buf, char c);
bool is_space_character(int c);
bool is_allowed_first_char(int c);
bool is_allowed_char(int c);
void parse_spaces(ParseContext ctxt);
HString get_name(ParseContext ctxt);
std::shared_ptr<Token> get_token(ParseContext ctxt);

