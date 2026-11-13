foo : Void -> ()
foo impossible

T : () -> Type
T () = Void

bar : (u : ()) -> T u -> ()
bar () impossible
