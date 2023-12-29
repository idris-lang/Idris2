import Language.Reflection

%language ElabReflection

data_decl : List Decl
data_decl = `[data T = A | B]

record_decl : List Decl
record_decl = `[record R where]

data_decl' : List Decl
data_decl' = `[public export data T = A | B]

record_decl' : List Decl
record_decl' = `[public export record R where]
