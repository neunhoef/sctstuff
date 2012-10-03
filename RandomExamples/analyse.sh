#!/bin/sh
grep Found *.result | perl -ne 'if (/randrel(\d+)_(\d+).nck.result:# Found (\d+)/) { ++$a[$1-25][$3]; }; END { print join("\n",map { join(", ",@$_) } @a) . "\n"; }'
