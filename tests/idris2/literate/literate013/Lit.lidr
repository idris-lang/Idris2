> module Lit
>
> %default total

a > b

a < b

> data V a = Empty | Extend a (V a)

> isCons : V a -> Bool
> isCons Empty = False
> isCons (Extend _ _) = True

< namespace Hidden
<   data U a = Empty | Extend a (U a)
