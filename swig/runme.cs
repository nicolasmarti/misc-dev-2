using System;

public class runme {
       static void Main(){

       Console.WriteLine("test start");

       ///////////////////////////////
       Test.t data = Test.t.ONE;
       Console.WriteLine( data );
       Test toto = new Test( data );
       Console.WriteLine( toto );
       Console.WriteLine( toto.data() );

       ///////////////////////////////
       Test.t data2 = Test.t.TWO;
       Console.WriteLine( data2 );
       Test tata = Test.create( data2 );
       Console.WriteLine( tata );
       Console.WriteLine( tata.data() );

       ///////////////////////////////
       Test.t data3 = Test.t.THREE;
       Console.WriteLine( data2 );
       Test tata2 = Test.create2( data3 );
       Console.WriteLine( tata2 );
       Console.WriteLine( tata2.data() );

       ///////////////////////////////
       Test.nums n = new Test.nums( 0, (float)(1.0), 1.0 );
       Console.WriteLine( n );
       
       Console.WriteLine("test stop");

       }
}