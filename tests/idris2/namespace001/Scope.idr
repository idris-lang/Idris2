-- Namespaces are currently allowed to be empty, as modules are, but also
-- require their contents to be indented to denote where they end.
-- Whereas a module's end is the end of the file.

-- Since there's no indentation on the latter definitions, this file should have
-- Test in scope under Main.X.Test, Test in scope under Main.Test, and nothing
-- in scope in Main.Y because namespace Y ends immediately.

namespace X
  private
  data Test = A | B

namespace Y
private
data Test = A | B
