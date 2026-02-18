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


weirdNo : {n : Nat} -> Nat
weirdNo {n } = ?weirdNo_rhs

weird0a : {n : Nat} -> Nat
weird0a {n= a} = ?weird0a_rhs

weird0b : {n : Nat} -> Nat
weird0b {n =b} = ?weird0b_rhs

weird1a : {n : Nat} -> Nat
weird1a { n= a} = ?weird1a_rhs

weird1b : {n : Nat} -> Nat
weird1b { n =b} = ?weird1b_rhs

weird2a : {n : Nat} -> Nat
weird2a {  n=  a} = ?weird2a_rhs

weird2b : {n : Nat} -> Nat
weird2b {  n  =b} = ?weird2b_rhs

weirdSpacedA : {n : Nat} -> Nat
weirdSpacedA {  n= a } = ?weirdSpacedA_rhs

weirdSpacedB : {n : Nat} -> Nat
weirdSpacedB {  n =b } = ?weirdSpacedB_rhs
