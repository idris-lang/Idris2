-- Testing that unbound implicits get lifted appropriately

-- Should all be at the top
comp : (b -> c) -> (a -> b) -> a -> c

-- Leave 'a' where it is
comp2 : (b -> c) -> {a : _} -> (a -> b) -> a -> c
