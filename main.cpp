#include "parser.h"
#include "system.h"
#include <iostream>
#include <fstream>

int main(int argc, char *argv[])
{
    if (argc != 2)
    {
        std::cout << "Usage: " << argv[0] << " <input_file>" << std::endl;
        return 1;
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

