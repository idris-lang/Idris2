f : Nat -> Nat
f n = case n of case_val => ?f_rhs

g : Nat -> Nat
g n = (case n of case_val => ?g_rhs)

h : Nat -> Nat
h n = (case n of
            case_val => ?h_rhs     )

data Test = One
          | Two Nat
          | Three String Nat
          | Four

toTest : Nat -> Test

i : Nat -> Nat
i n = case toTest n of case_val => ?i_rhs

j : Nat -> Nat
j n = j_Where n where
  j_Where : Nat -> Nat
  j_Where k = (case toTest k of case_val => ?j_Where_rhs    )

k : Nat -> Nat
k n = (case toTest n of
            case_val => ?k_rhs)

l : Nat -> Nat -> Unit
l n m = case n of foo => case toTest m of case_val => ?l_rhs

m : Nat -> Nat -> Unit
m n k = (case n of foo => case toTest k of case_val => ?m_rhs  )

n : Nat -> Nat -> Unit
n k m = case k of foo => case toTest m of
                              case_val => ?n_rhs

o : Nat -> Nat -> Unit
o n m = (case n of foo => case toTest m of
                               case_val => ?o_rhs   )

