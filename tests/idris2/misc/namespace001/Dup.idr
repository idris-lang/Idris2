-- Namespaces are currently allowed to be empty, as modules are, but also
-- require their contents to be indented to denote where they end.
-- Whereas a module's end is the end of the file.

-- Since there's no indentation each namespace ends imediately. So each Test
-- defines things at the module level, causing an `already defined` error.

namespace X
private
data Test = A | B

namespace Y
private
data Test = A | B
