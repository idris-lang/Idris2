module Spacing

no : {n : Nat} -> Nat
no {n} = ?no_rhs

spaced : {n : Nat} -> Nat
spaced { n } = ?spaced_rhs

s1 : {n : Nat} -> Nat
s1 { n} = ?s1_rhs

s2 : {n : Nat} -> Nat
s2 {  n} = ?s2_rhs

s3 : {n : Nat} -> Nat
s3 {   n} = ?s3_rhs


noSEq : {n : Nat} -> Nat
noSEq {n = a} = ?noSEq_rhs

spacedEq : {n : Nat} -> Nat
spacedEq { n = a } = ?spacedEq_rhs

s1Eq : {n : Nat} -> Nat
s1Eq { n = a} = ?s1Eq_rhs

s2Eq : {n : Nat} -> Nat
s2Eq {  n = a} = ?s2Eq_rhs

s3Eq : {n : Nat} -> Nat
s3Eq {   n = a} = ?s3Eq_rhs

