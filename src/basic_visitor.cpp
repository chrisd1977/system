#include "basic_visitor.h"
#include <ostream>

void BasicVisitor::accept(const Basic &b) {}

void BasicVisitor::accept(const Identifier &ident)
{
   accept((const Basic&)ident);
}

void BasicVisitor::accept(const Prop &b)
{
   accept((const Basic&)b);
}

void BasicVisitor::accept(const Type &t)
{
   accept((const Basic&)t);
}

void BasicVisitor::accept(const TypeSucc &t)
{
   accept((const Basic&)t);
}

void BasicVisitor::accept(const TypeMax &t)
{
   accept((const Basic&)t);
}

void BasicVisitor::accept(const BindVariable &bv)
{
   accept((const Basic&)bv);
}

void BasicVisitor::accept(const Forall &fa)
{
   accept((const BindVariable&)fa);
}

void BasicVisitor::accept(const Lambda &lm)
{
   accept((const BindVariable&)lm);
}

void BasicVisitor::accept(const Apply &a)
{
   accept((const Basic&)a);
}

/*********************
 * Printing of terms *
 *********************/

class PrintVisitor: public BasicVisitor
{
public:
   PrintVisitor(std::ostream &os): os(os) {}
   void accept(const Identifier &ident) override
   {
      os << ident.module_name << '.' << ident.name;
   }
   void accept(const Prop &b) override
   {
      os << "Prop";
   }
   void accept(const Type &t) override
   {
      os << "Type";
   }
   void accept(const TypeSucc &t) override
   {
      os << "TypeSucc(" << t.arg << ')';
   }
   void accept(const TypeMax &tm) override
   {
      os << "TypeMax(" << tm.arg1 << ", " << tm.arg2 << ')';
   }
   void accept(const BindVariable &bv) override
   {
      os << (typeid(bv) == typeid(Forall) ? "(forall " : "(lambda ")
         << bv.var << ": " << bv.type << ", " << bv.body << ")";
   }
   void accept(const Apply &a) override
   {
      os << "(" << a.function << " " << a.argument << ")";
   }
private:
   std::ostream &os;
};

std::ostream &operator<<(std::ostream &os, const Term &t)
{
   PrintVisitor vis(os);
   t.ptr->visit(vis);
   return os;
}

/************************
 * head_reduce function *
 ************************/

class HeadReduceVisitor: public BasicVisitor
{
public:
   HeadReduceVisitor(Environment &e): e(e) {}
   void accept(const Basic &b) override
   {
      result = b.shared_from_this();
   }
   void accept(const Identifier &ident) override
   {
      result = ident.normalize(e).ptr;
   }
   void accept(const Apply &a) override
   {
      Term new_function = ::head_reduce(e, a.function);
      std::shared_ptr<const Lambda> lambda
         = std::dynamic_pointer_cast<const Lambda>(new_function.ptr);
      if (lambda)
         result = lambda->body.ptr->subst(lambda->var, a.argument).ptr;
      else if (new_function.ptr == a.function.ptr)
         result = a.shared_from_this();
      else
         result = std::make_shared<Apply>(new_function, a.argument);
   }
public:
   Environment &e;
   std::shared_ptr<const Basic> result;
};

Term head_reduce(Environment &e, const Term &t)
{
   std::shared_ptr<const Basic> result = t.ptr;
   while (true)
   {
      HeadReduceVisitor vis(e);
      result->visit(vis);
      if (vis.result == result)
         return result;
      result = vis.result;
   }
   return result;
}

