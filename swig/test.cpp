#include "test.hpp"

Test::Test( t data ): m_data( data ){
  std::cout << "Test constructor" << std::endl << std::flush;
};

Test::~Test(){
  std::cout << "Test destructor" << std::endl << std::flush;
};

std::shared_ptr< Test > Test::create( t data ){
  std::shared_ptr< Test > result;
  result = std::make_shared< Test >( data );
  return result;
}

Test_ptr_t Test::create2( t data ){
  Test_ptr_t result;
  result = Test_ptr_t( new Test( data ) );
  return result;
}

Test::t Test::data(){
  return m_data;
}
