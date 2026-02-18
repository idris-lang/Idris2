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

%deprecate
export
dep3 : String -> String
dep3 x = x ++ "!"

%deprecate
public export
0 foo : (0 a : Type) -> Type
foo x = List x
