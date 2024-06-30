#include "basic.h"

class BasicVisitor
{
public:
   virtual void accept(const Basic &b);
   virtual void accept(const Identifier &ident);
   virtual void accept(const Prop &b);
   virtual void accept(const Type &t);
   virtual void accept(const TypeSucc &t);
   virtual void accept(const TypeMax &t);
   virtual void accept(const BindVariable &bv);
   virtual void accept(const Forall &fa);
   virtual void accept(const Lambda &lm);
   virtual void accept(const Apply &a);
};

std::ostream &operator<<(std::ostream &os, const Term &t);

Term head_reduce(Environment &e, const Term &t);

