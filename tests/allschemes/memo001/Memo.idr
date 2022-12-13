-- This tests checks, whether toplevel constants are
-- properly memoized. If they are not, this test
-- will perform 10^20 additions and will therefore not
-- finish in reasonable time.
n0 : Nat
n0 = 1

n1 : Nat
n1 = n0 + n0 + n0 + n0 + n0 + n0 + n0 + n0 + n0 + n0

n2 : Nat
n2 = n1 + n1 + n1 + n1 + n1 + n1 + n1 + n1 + n1 + n1

n3 : Nat
n3 = n2 + n2 + n2 + n2 + n2 + n2 + n2 + n2 + n2 + n2

n4 : Nat
n4 = n3 + n3 + n3 + n3 + n3 + n3 + n3 + n3 + n3 + n3

n5 : Nat
n5 = n4 + n4 + n4 + n4 + n4 + n4 + n4 + n4 + n4 + n4

n6 : Nat
n6 = n5 + n5 + n5 + n5 + n5 + n5 + n5 + n5 + n5 + n5

n7 : Nat
n7 = n6 + n6 + n6 + n6 + n6 + n6 + n6 + n6 + n6 + n6

n8 : Nat
n8 = n7 + n7 + n7 + n7 + n7 + n7 + n7 + n7 + n7 + n7

n9 : Nat
n9 = n8 + n8 + n8 + n8 + n8 + n8 + n8 + n8 + n8 + n8

n10 : Nat
n10 = n9 + n9 + n9 + n9 + n9 + n9 + n9 + n9 + n9 + n9

n11 : Nat
n11 = n10 + n10 + n10 + n10 + n10 + n10 + n10 + n10 + n10 + n10

n12 : Nat
n12 = n11 + n11 + n11 + n11 + n11 + n11 + n11 + n11 + n11 + n11

n13 : Nat
n13 = n12 + n12 + n12 + n12 + n12 + n12 + n12 + n12 + n12 + n12

n14 : Nat
n14 = n13 + n13 + n13 + n13 + n13 + n13 + n13 + n13 + n13 + n13

n15 : Nat
n15 = n14 + n14 + n14 + n14 + n14 + n14 + n14 + n14 + n14 + n14

n16 : Nat
n16 = n15 + n15 + n15 + n15 + n15 + n15 + n15 + n15 + n15 + n15

n17 : Nat
n17 = n16 + n16 + n16 + n16 + n16 + n16 + n16 + n16 + n16 + n16

n18 : Nat
n18 = n17 + n17 + n17 + n17 + n17 + n17 + n17 + n17 + n17 + n17

n19 : Nat
n19 = n18 + n18 + n18 + n18 + n18 + n18 + n18 + n18 + n18 + n18

n20 : Nat
n20 = n19 + n19 + n19 + n19 + n19 + n19 + n19 + n19 + n19 + n19

main : IO ()
main = do printLn n20
