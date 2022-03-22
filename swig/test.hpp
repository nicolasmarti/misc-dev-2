#include <iostream>
#include <memory>
class Test;
typedef std::shared_ptr<const Test> Test_ptr_t;
class Test{
public:
  enum t { ZERO, ONE, TWO, THREE };
  Test( t data );
  ~Test();
  static std::shared_ptr< Test > create( t data );
  static Test_ptr_t create2( t data );
  t data();
  struct nums{

    nums( int i, float f, double d ): m_int(i), m_float( f ), m_double( d ){
      std::cout << "nums constructor" << std::endl << std::flush;
    };
    ~nums(){
      std::cout << "nums destructor" << std::endl << std::flush;
    };
    
    int m_int;
    float m_float;
    double m_double;
  };
private:
  t m_data;
};
