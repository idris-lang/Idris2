import Data.Nat
import Data.Vect
import Language.Reflection

%language ElabReflection

axes : (n : Nat) -> {auto gt : GT n 0} -> {auto lte : LTE n 4} -> Vect n String
axes 1 = ["x"]
axes 2 = "y" :: axes 1
axes 3 = "z" :: axes 2
axes 4  = "w" :: axes 3
axes (S (S (S (S (S _))))) {lte = (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc _)))))} impossible

mkPoint : (n : Nat) -> {auto gt : GT n 0} -> {auto lte : LTE n 4} -> Decl
mkPoint n
    = let type = "Point" ++ show n ++ "D" in
      IRecord emptyFC Public
      (MkRecord emptyFC (NS (MkNS ["Main"]) (UN type)) [] (NS (MkNS ["Main"]) (UN ("Mk" ++ type)))
        (toList $ map (\axis => MkIField emptyFC MW ExplicitArg (UN axis) `(Double)) (axes n)))

logDecls : TTImp -> Elab (Int -> Int)
logDecls v
    = do declare [IClaim EmptyFC MW Public []
                 (MkTy EmptyFC `{{ Main.foo }}
                               `(Int -> Int -> Int) )]

         declare `[ foo x y = x + y ]

         declare [ mkPoint 3 ]

         declare `[ multBy : Int -> Int
                    multBy x = x * ~(v) ]
         declare `[ myplus : Nat -> Nat -> Nat
                    myplus Z y = y
                    myplus (S k) y = S (myplus k y) ]
         check `( multBy )

mkMult : Int -> Int
mkMult = %runElab logDecls `(4)

point : Point3D
point = MkPoint3D 1.0 2.0 3.0
