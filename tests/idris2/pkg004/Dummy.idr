module Dummy

something : String
something = "Something something"

data Proxy : Type -> Type where
  MkProxy : Proxy a
