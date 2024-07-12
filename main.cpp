#include "parser.h"
#include "system.h"
#include <iostream>
#include <fstream>
#include <cstring>

int main(int argc, char *argv[])
{
    if (argc != 2)
    {
        std::cout << "Usage: " << argv[0] << " <input_file>" << std::endl;
        std::cout << "Usage: " << argv[0] << " --version" << std::endl;
        return 1;
    }
    if (!strcmp(argv[1], "--version"))
    {
        std::cout << "System version " VERSION << std::endl;
        return 0;
    }
    std::filebuf buf;
    if (!buf.open(argv[1], std::ios_base::in))
        std::cout << "Could not open file " << argv[1] << std::endl;
    Environment e;
    CommandParser parser(e, { LIBDIR , "." });
    try
    {
        parse_streambuf(buf, argv[1], parser);
    }
    catch (std::runtime_error &err)
    {
        std::cout << err.what() << std::endl;
        return 1;
    }
    return 0;
}

