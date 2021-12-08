import Data.Nat
import Data.Vect
import Language.Reflection

%language ElabReflection

fc : FC
fc = EmptyFC

quoteTest : TTImp -> TTImp -> List Decl
quoteTest f arg = `[ myFunc : ~(IApp fc f arg) ]

axes : (n : Nat) -> {auto gt : GT n 0} -> {auto lte : LTE n 4} -> Vect n String
axes 1 = ["x"]
axes 2 = "y" :: axes 1
axes 3 = "z" :: axes 2
axes 4  = "w" :: axes 3
axes (S (S (S (S (S _))))) {lte} = absurd lte

mkPoint : (n : Nat) -> {auto gt : GT n 0} -> {auto lte : LTE n 4} -> Decl
mkPoint n
    = let type = "Point" ++ show n ++ "D" in
      let mkMainUN = NS (MkNS ["Main"]) . UN . Basic in
      IRecord emptyFC Nothing Public Nothing
      (MkRecord emptyFC (mkMainUN type) [] (mkMainUN ("Mk" ++ type))
        (toList $ map (\axis => MkIField emptyFC MW ExplicitArg (UN (Field axis)) `(Double)) (axes n)))

logDecls : TTImp -> Elab (Int -> Int)
logDecls v
    = do declare [IClaim EmptyFC MW Public []
                 (MkTy EmptyFC EmptyFC `{ Main.foo }
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
