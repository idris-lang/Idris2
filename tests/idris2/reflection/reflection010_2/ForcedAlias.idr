module ForcedAlias

data Two a = TwoC a
           | Other

forcedAlias : Two Int -> Int
forcedAlias x = case x of
  TwoC {a = e @ .(Int)} y => the e y
  Other => 0

test : forcedAlias (TwoC 10) = 10
test = Refl
