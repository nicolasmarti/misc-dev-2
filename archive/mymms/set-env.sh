#!/bin/bash
mydir=`pwd`
currdir=`dirname $0`
finaldir="$mydir/$currdir"

export PATH="$finaldir/src/app/mymms:$PATH"
export MYMMS_STDLIB_PATH="$finaldir/stdlib"