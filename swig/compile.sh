rm -Rf SWIGTYPE_p_std__shared_ptrT_Test_t.cs test.cs Test.cs *.o *.so *.exe *CPPCSHARP* t.cs testPINVOKE.cs test_wrap.cxx
swig -csharp -c++ test.i
g++ -c -fpic test.cpp test_wrap.cxx
g++ -shared test.o test_wrap.o -o libtest.so
mcs -sdk:4 -out:runme.exe *.cs 
#csharp -sdk:4 -out:runme.exe -lib:./ *.cs
./runme.exe
rm -Rf SWIGTYPE_p_std__shared_ptrT_Test_t.cs test.cs Test.cs *.o *.so *.exe *CPPCSHARP* t.cs testPINVOKE.cs test_wrap.cxx
