#include "partial_parse_level.h"

class PartialParse
{
public:
   typedef std::vector<std::shared_ptr<PartialParseLevel>> ParseStack;
   PartialParse() = default;
   PartialParse(const PartialParse&);
   virtual ~PartialParse() = default;
   virtual std::shared_ptr<PartialParse> clone() const = 0;
   void copy_stack(const ParseStack &stack);
   void print(std::ostream &os) const;
   int size() const;
   std::shared_ptr<const ParseRule> get_toplevel_rule() const;
   void add_rule(std::shared_ptr<ParseTermRule> rule);
   bool matches(const Token &tok) const;
   bool toplevel_is_complete() const;
   void process(const Token &tok);
   void process(Term &t);
   bool parse_is_complete() const;
   Term pop_off_toplevel_term();
protected:
   ParseStack parse_stack;
};

std::ostream &operator<<(std::ostream &os, const PartialParse &pp);

class PartialParseTerm: public PartialParse
{
public:
   PartialParseTerm(bool add_default_rule = true);
   std::shared_ptr<PartialParse> clone() const override;
   Term get_finished_parse_result() const;
};

class PartialParseCommand: public PartialParse
{
public:
   PartialParseCommand(std::shared_ptr<const ParseCommandRule> rule = nullptr);
   std::shared_ptr<PartialParse> clone() const override;
   void process_parse_result();
};

