data SimpleData = PtrAndSize AnyPtr Int

record Complicated where
  constructor MkComplicated
  simple : SimpleData

record MoreComplicated where
    constructor MkMoreComplicated
    something : Complicated

record EvenMoreComplicated where
    constructor MkEvenMoreComplicated
    somethingEven : MoreComplicated

data TooComplicatedToBeTrue : (something : EvenMoreComplicated) -> Type where
    SomethingVeryComplicatedIs :
        TooComplicatedToBeTrue
            (MkEvenMoreComplicated (MkMoreComplicated (MkComplicated (PtrAndSize addr len))))

showing  :  (something : EvenMoreComplicated) -> (TooComplicatedToBeTrue something) -> Void
showing _ SomethingVeryComplicatedIs impossible
