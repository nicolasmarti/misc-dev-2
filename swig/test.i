%module test

%include<std_shared_ptr.i>

// required
%shared_ptr(Test)
%shared_ptr(model)


%{
  /* Includes the header in the wrapper code */
#include "test.hpp"
  %}
 
/* Parse the header file to generate wrappers */
%include "test.hpp"
