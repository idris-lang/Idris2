module Foo

%deprecate
export
dep1 : String
dep1 = "hello"

||| Just use the string "world" directly from now on.
%deprecate
export
dep2 : String
dep2 = "world"
