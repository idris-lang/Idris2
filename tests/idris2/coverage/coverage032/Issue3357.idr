namespace PrimInt
  0 oops : (0 x : Int) -> if x == 0 then Unit else Void
  oops 0 = ()

  boom : Void
  boom = void (oops 1)

namespace PrimString
  0 oops : (0 x : String) -> if x == "" then Unit else Void
  oops "" = ()

  boom : Void
  boom = void (oops "foo")

namespace PrimTy
  0 oops : (0 a : Type) -> a
  oops Int = 0

  boom : Void
  boom = void (oops Void)

namespace TyCon
  0 oops : (0 a : Type) -> a
  oops Nat = Z

  boom : Void
  boom = void (oops Void)

namespace Type
  0 oops : (0 a : Type) -> a
  oops Type = Type

  boom : Void
  boom = void (oops Void)
