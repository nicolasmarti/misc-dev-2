#!/bin/sh

set -e

TESTS=tests.otarget
APPS=apps.otarget
FLAGS=""
OCAMLBUILD=ocamlbuild

ocb()
{
  $OCAMLBUILD $FLAGS $*
}

rule() {
  case $1 in
    clean)  ocb -clean;;
    all)    ocb $TESTS; ocb $APPS;;
    tests)  ocb $TESTS;;	  
    apps)   ocb $APPS;;
    *)      echo "Unknown action $1";;
  esac;
}

if [ $# -eq 0 ]; then
  rule all
else
  while [ $# -gt 0 ]; do
    rule $1;
    shift
  done
fi

