interface Happy t where
  happy : t

Happy Nat where
  happy = Z

Happy Bool where
  happy = True
