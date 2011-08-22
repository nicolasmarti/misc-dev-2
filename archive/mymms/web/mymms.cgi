#!/bin/which perl

use CGI;
$q = new CGI;

$program = "../src/app/mymms -w";

print "Content-type: text/html\n\n";
print "<HTML><HEAD><TITLE>Result</TITLE></HEAD><BODY><PRE>\n";
$|=1;

open FIN, "| $program";
print FIN $q->param('input');
close FIN;

print "</PRE></BODY></HTML>\n";



