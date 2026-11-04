module A

import B

-- A rule on a name from another module, with a visible right-hand side.
%transform "fooRule" B.foo n = 100
