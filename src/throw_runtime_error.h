#include <sstream>

class ThrowRuntimeError
{
public:
   ~ThrowRuntimeError() noexcept(false)
   {
      throw std::runtime_error(os.str());
   }
   template <class T>
   std::ostream &operator<<(T&& t)
   {
      return os << t;
   }
private:
   std::ostringstream os;
};

