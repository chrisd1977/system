#include "system.h"

class TemporaryAxiom
{
public:
   TemporaryAxiom(Environment &e, HString n, const Term &t);
   ~TemporaryAxiom();
private:
   Environment &e;
};

