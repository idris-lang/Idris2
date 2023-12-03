#!/bin/awk -f
# consistently replace numbers in arg:NNN conArg:NNN and $resolvedNNN  
BEGIN { count = 1 }
{
    out = ""
    while (match($0, /(arg:|conArg:|[$]resolved)[0-9]*/)) {
        rs = RSTART
        rl = RLENGTH
        m = substr($0, rs, rl - 1)
        pfx = "$resolved"
        if (match(m,/arg:/)) { pfx = "arg:" }
        if (match(m,/conArg:/)) { pfx = "conArg:" }
        if (!(m in mapping)) {
            mapping[m] = count
            count++
        }
        out = out substr($0, 1, rs - 1) pfx mapping[m]
        $0 = substr($0, rs + rl)
    }
    print out $0
}
