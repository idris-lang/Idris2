module GetVis

import Language.Reflection

private fooPriv : Int
export fooExp : Int
public export fooPubExp : Int

namespace A
  private foo : Int

namespace B
  export foo : Int

namespace C
  public export foo : Int
