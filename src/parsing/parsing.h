#include "system.h"
#include <string>

Term parse(const std::string &s);

void parse_environment(std::streambuf &buf, Environment& e,
                       std::vector<std::string> path);

