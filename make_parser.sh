#!/bin/bash
cd tip-lib/src
bnfc -p Tip.Parser TIP.bnfc
# happy -gca Tip/Parser/ParTIP.y
# alex -g Tip/Parser/LexTIP.x
