#include "temporary_axiom.h"

TemporaryAxiom::TemporaryAxiom(Environment &e, HString n, const Term &t):
       e(e)
{
    e.axiom(n, t, false);
}

TemporaryAxiom::~TemporaryAxiom()
{
   e.pop();
}

