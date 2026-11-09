namespace A
  private
  B : Type
  B = Type

  -- breaks the privateness of B
  record C where
    constructor MkC

D : Type
D = B  -- should fail
