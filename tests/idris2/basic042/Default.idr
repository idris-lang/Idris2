module Default

public export
interface Default ty where
    default : ty

public export
Default Nat where
    default = Z

public export
Default Bool where
    default = False

public export
foo : {default : Bool} -> Bool
foo {default} = default

public export
bar : {default True b : Bool} -> Bool
bar {b} = b
