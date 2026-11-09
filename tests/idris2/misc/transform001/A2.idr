module A2

import B

-- A second rule for the same function, from a module imported after A.
%transform "fooRule2" B.foo n = 300
