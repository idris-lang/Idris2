--------------
-- Explicit --
--------------

namespace EI
  f : Type -> Type -> Type
  g : Type -> {_ : Type} -> Type
  g = f

namespace EA
  f : Type -> Type -> Type
  g : Type -> {auto _ : Type} -> Type
  g = f

namespace ED
  f : Type -> Type -> Type
  g : Type -> {default Int _ : Type} -> Type
  g = f

--------------
-- Implicit --
--------------

namespace IE
  f : Type -> {_ : Type} -> Type
  g : Type -> Type -> Type
  g = f

namespace IA
  f : Type -> {_ : Type} -> Type
  g : Type -> {auto _ : Type} -> Type
  g = f

namespace ID
  f : Type -> {_ : Type} -> Type
  g : Type -> {default Int _ : Type} -> Type
  g = f

----------
-- Auto --
----------

namespace AE
  f : Type -> {auto _ : Type} -> Type
  g : Type -> Type -> Type
  g = f

namespace AI
  f : Type -> {auto _ : Type} -> Type
  g : Type -> {_ : Type} -> Type
  g = f

namespace AD
  f : Type -> {auto _ : Type} -> Type
  g : Type -> {default Int _ : Type} -> Type
  g = f

-------------
-- Default --
-------------

namespace DE
  f : Type -> {default Int _ : Type} -> Type
  g : Type -> Type -> Type
  g = f

namespace DI
  f : Type -> {default Int _ : Type} -> Type
  g : Type -> {_ : Type} -> Type
  g = f

namespace DA
  f : Type -> {default Int _ : Type} -> Type
  g : Type -> {auto _ : Type} -> Type
  g = f

