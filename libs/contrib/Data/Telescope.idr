||| A telescope is the variable context in a dependently typed program.
||| Dependent types with free varialbes  are really only well-defined in a telescope.
|||
||| A segment of a telescope is a tuple of types in that
||| telescope. These are usually implicit in formal developments, but
||| seem to be crucial to get a compositional account. Here we use
||| them to get 'n-ary dependent function' (compare with `Data.Fun`
||| and `Data.Rel`).
|||
||| I've learned this from Conor McBride on an SPLV'19 bus ride.
||| A literary reference would be welcome. This paper is a start:
||| Unifiers as Equivalences: Proof-Relevant Unification of Dependently Typed Data.
||| Jesper Cockx, Dominique Devriese, Frank Piessens, ICFP'16.
||| but they don't seem to have segments and their left action on contexts.
module Data.Telescope

import public Data.Telescope.Telescope
import public Data.Telescope.Segment
import public Data.Telescope.SimpleFun
import public Data.Telescope.Fun
import public Data.Telescope.Congruence
