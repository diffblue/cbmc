#!/bin/sh
echo "Simplifying $1..."
goto-analyzer $1 --constant-propagation --simplify --dump-c simplified.c
sed -i -e 's/#/_/g' simplified.c
sed -i -e 's/_include/#include/g' simplified.c
sed -i -e 's/_ifndef/#ifndef/g' simplified.c
sed -i -e 's/_define/#define/g' simplified.c
sed -i -e 's/_endif/#endif/g' simplified.c


