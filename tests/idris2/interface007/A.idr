module A

-- Check that this doesn't go into a loop when resolving Show. because
-- f itself is a candidate when elaborating the top level f function!
public export
interface F (p : Type -> Type) where
  f : Show a => p a -> a
