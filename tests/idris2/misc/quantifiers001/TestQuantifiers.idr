import Decidable.Decidable

import Data.Nat
import Data.Vect
import Data.List.Quantifiers
import Data.Vect.Quantifiers
import Data.SnocList.Quantifiers


namespace List
  public export
  aList : List Nat
  aList = [1, 1, 1]

  export
  testAll : {auto 0 prf : IsYes (List.Quantifiers.All.all Data.Nat.isItSucc Main.List.aList)}
          -> ()
  testAll = ()

  export
  testAny : {auto 0 prf : IsYes (List.Quantifiers.Any.any Data.Nat.isItSucc Main.List.aList)}
          -> ()
  testAny = ()

namespace Vect
  public export
  aVect : Vect 3 Nat
  aVect = [1, 1, 1]

  export
  testAll : {auto 0 prf : IsYes (Vect.Quantifiers.All.all Data.Nat.isItSucc Main.Vect.aVect)}
          -> ()
  testAll = ()

  export
  testAny : {auto 0 prf : IsYes (Vect.Quantifiers.Any.any Data.Nat.isItSucc Main.Vect.aVect)}
          -> ()
  testAny = ()

namespace SnocList
  public export
  aSnocList : SnocList Nat
  aSnocList = [< 1, 1, 1]

  export
  testAll : {auto 0 prf : IsYes (SnocList.Quantifiers.All.all Data.Nat.isItSucc Main.SnocList.aSnocList)}
          -> ()
  testAll = ()

  export
  testAny : {auto 0 prf : IsYes (SnocList.Quantifiers.Any.any Data.Nat.isItSucc Main.SnocList.aSnocList)}
          -> ()
  testAny = ()
