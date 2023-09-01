works : (n : (Nat, Nat)) ->
        let mk = n in
            {y : Bool} -> (z : Bool) -> String
works (m, k) {y} z = ?h1

FailType : (Nat, Nat) -> Type
FailType (m, k) = {y : Bool} -> (z : Bool) -> String

fails : (n : (Nat, Nat)) -> FailType n
fails (m, k) {y} z = ?h2

fails2 : (n : (Nat, Nat)) ->
         let (m, k) = n in
             {y : Bool} -> (z : Bool) -> String
fails2 (m, k) {y} z = ?h3
