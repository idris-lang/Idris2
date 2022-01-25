
namespace A
  export
  x : Bool -> Bool
  x = not

namespace B
  export
  x : Nat -> Bool
  x Z = True
  x _ = False

%ambiguity_depth 1000

-- There's an undefined name very deep here - if we don't take a shortcut,
-- this shows all the ambiguous branches with the undefined named!
test : Nat -> Bool
test val
    = x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $
      x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ x $ va
