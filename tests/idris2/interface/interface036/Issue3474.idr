interface Iface1 where
  method1 : Type -> {_ : Type} -> Type

interface Iface2 where
  method2 : {x : Type} -> Type

interface Iface3 where
  method3 : (x : Type) => Type

interface Iface4 where
  method4 : Type => Type => Type

interface Iface5 where
  method5 : {X : Type} -> Type

interface Iface6 where
  method6 : (X : Type) => Type

interface Iface7 where
  method7 : {_ : Type} -> Type

interface Iface8 where
  method8 : {x : Type} -> {x : Int} -> {_ : String} -> (x : Double) => {x : Integer} -> Type
