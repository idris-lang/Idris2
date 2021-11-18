||| N-ary congruence for reasoning
module Data.Telescope.Congruence

import Data.Telescope.Telescope
import Data.Telescope.Segment
import Data.Telescope.SimpleFun
import Data.Telescope.Fun

public export
congType : (delta : Segment n gamma)
  -> (env1 : Left.Environment gamma) -> (sy1 : SimpleFun env1 delta Type) -> (lhs : Fun env1 delta sy1)
  -> (env2 : Left.Environment gamma) -> (sy2 : SimpleFun env2 delta Type) -> (rhs : Fun env2 delta sy2)
  -> Type
congType []            env1 sy1 lhs  env2 sy2 rhs = lhs ~=~ rhs
congType (ty :: delta) env1 sy1 lhs  env2 sy2 rhs =
                         {x1 : ty env1} -> {x2 : ty env2}
                      -> x1 ~=~ x2
                      -> congType delta
                           (env1 ** x1) (sy1 x1) (lhs x1)
                           (env2 ** x2) (sy2 x2) (rhs x2)

public export
congSegment : {n : Nat} -> (0 delta : Segment n gamma)
  ->(0 env1 : Left.Environment gamma)-> (0 sy1 : SimpleFun env1 delta Type) -> (0 lhs : Fun env1 delta sy1)
  ->(0 env2 : Left.Environment gamma)-> (0 sy2 : SimpleFun env2 delta Type) -> (0 rhs : Fun env2 delta sy2)
  ->(0 _ : env1 ~=~ env2)      -> (0 _ : sy1 ~=~ sy2)                 -> (0 _ : lhs ~=~ rhs)
  -> congType delta env1 sy1 lhs
                    env2 sy2 rhs
congSegment {n = 0  } []            env sy context env sy context Refl Refl Refl = Refl
congSegment {n = S n} (ty :: delta) env sy context env sy context Refl Refl Refl = recursiveCall
  where
    recursiveCall : {x1 : ty env} -> {x2 : ty env} -> x1 ~=~ x2
                 -> congType delta (env ** x1) (sy x1) (context x1)
                                   (env ** x2) (sy x2) (context x2)
    recursiveCall {x1=x} {x2=x} Refl = congSegment delta
                                                   (env ** x) (sy x) (context x)
                                                   (env ** x) (sy x) (context x)
                                                   Refl       Refl   Refl

public export
cong : {n : Nat} -> {0 delta : Segment n []} -> {0 sy : SimpleFun () delta Type}
    -> (context : Fun () delta sy)
    -> congType delta () sy context
                      () sy context
cong {n} {delta} {sy} context = congSegment delta ()    sy   context
                                                  ()    sy   context
                                                  Refl  Refl Refl
