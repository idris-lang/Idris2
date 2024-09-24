-- This tests checks, whether lazy values constants are
-- properly memoized. If they are not, this test
-- will perform 10^20 additions and will therefore not
-- finish in reasonable time.
n0 : Lazy Nat
n0 = 1

n1 : Lazy Nat
n1 = n0 + n0 + n0 + n0 + n0 + n0 + n0 + n0 + n0 + n0

n2 : Lazy Nat
n2 = n1 + n1 + n1 + n1 + n1 + n1 + n1 + n1 + n1 + n1

n3 : Lazy Nat
n3 = n2 + n2 + n2 + n2 + n2 + n2 + n2 + n2 + n2 + n2

n4 : Lazy Nat
n4 = n3 + n3 + n3 + n3 + n3 + n3 + n3 + n3 + n3 + n3

n5 : Lazy Nat
n5 = n4 + n4 + n4 + n4 + n4 + n4 + n4 + n4 + n4 + n4

n6 : Lazy Nat
n6 = n5 + n5 + n5 + n5 + n5 + n5 + n5 + n5 + n5 + n5

n7 : Lazy Nat
n7 = n6 + n6 + n6 + n6 + n6 + n6 + n6 + n6 + n6 + n6

n8 : Lazy Nat
n8 = n7 + n7 + n7 + n7 + n7 + n7 + n7 + n7 + n7 + n7

n9 : Lazy Nat
n9 = n8 + n8 + n8 + n8 + n8 + n8 + n8 + n8 + n8 + n8

n10 : Lazy Nat
n10 = n9 + n9 + n9 + n9 + n9 + n9 + n9 + n9 + n9 + n9

n11 : Lazy Nat
n11 = n10 + n10 + n10 + n10 + n10 + n10 + n10 + n10 + n10 + n10

n12 : Lazy Nat
n12 = n11 + n11 + n11 + n11 + n11 + n11 + n11 + n11 + n11 + n11

n13 : Lazy Nat
n13 = n12 + n12 + n12 + n12 + n12 + n12 + n12 + n12 + n12 + n12

n14 : Lazy Nat
n14 = n13 + n13 + n13 + n13 + n13 + n13 + n13 + n13 + n13 + n13

n15 : Lazy Nat
n15 = n14 + n14 + n14 + n14 + n14 + n14 + n14 + n14 + n14 + n14

n16 : Lazy Nat
n16 = n15 + n15 + n15 + n15 + n15 + n15 + n15 + n15 + n15 + n15

n17 : Lazy Nat
n17 = n16 + n16 + n16 + n16 + n16 + n16 + n16 + n16 + n16 + n16

n18 : Lazy Nat
n18 = n17 + n17 + n17 + n17 + n17 + n17 + n17 + n17 + n17 + n17

n19 : Lazy Nat
n19 = n18 + n18 + n18 + n18 + n18 + n18 + n18 + n18 + n18 + n18

n20 : Lazy Nat
n20 = n19 + n19 + n19 + n19 + n19 + n19 + n19 + n19 + n19 + n19

main : IO ()
main = do printLn n20
