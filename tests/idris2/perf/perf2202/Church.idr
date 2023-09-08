Ty : Type
Ty = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty : Ty
empty = \ _, empty, _ => empty

arr : Ty -> Ty -> Ty
arr = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con : Type
Con = (Con : Type)
 ->(nil  : Con)
 ->(snoc : Con -> Ty -> Con)
 -> Con

nil : Con
nil = \ con, nil, snoc => nil

snoc : Con -> Ty -> Con
snoc = \ g, a, con, nil, snoc => snoc (g con nil snoc) a

Var : Con -> Ty -> Type
Var = \ g, a =>
    (Var : Con -> Ty -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var (snoc g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var g a -> Var (snoc g b) a)
 -> Var g a

vz : {g : _}-> {a : _} -> Var (snoc g a) a
vz = \ var, vz, vs => vz _ _

vs : {g : _} -> {B : _} -> {a : _} -> Var g a -> Var (snoc g B) a
vs = \ x, var, vz, vs => vs _ _ _ (x var vz vs)

Tm : Con -> Ty -> Type
Tm = \ g, a =>
    (Tm    : Con -> Ty -> Type)
 -> (var   : (g : _) -> (a : _) -> Var g a -> Tm g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm (snoc g a) B -> Tm g (arr a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm g (arr a B) -> Tm g a -> Tm g B)
 -> Tm g a

var : {g : _} -> {a : _} -> Var g a -> Tm g a
var = \ x, tm, var, lam, app => var _ _ x

lam : {g : _} -> {a : _} -> {B : _} -> Tm (snoc g a) B -> Tm g (arr a B)
lam = \ t, tm, var, lam, app => lam _ _ _ (t tm var lam app)

app : {g:_}->{a:_}->{B:_} -> Tm g (arr a B) -> Tm g a -> Tm g B
app = \ t, u, tm, var, lam, app => app _ _ _ (t tm var lam app) (u tm var lam app)

v0 : {g:_}->{a:_} -> Tm (snoc g a) a
v0 = var vz

v1 : {g:_}->{a:_}-> {B:_}-> Tm (snoc (snoc g a) B) a
v1 = var (vs vz)

v2 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm (snoc (snoc (snoc g a) B) C) a
v2 = var (vs (vs vz))

v3 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm (snoc (snoc (snoc (snoc g a) B) C) D) a
v3 = var (vs (vs (vs vz)))

v4 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm (snoc (snoc (snoc (snoc (snoc g a) B) C) D) E) a
v4 = var (vs (vs (vs (vs vz))))

test : {g:_}-> {a:_} -> Tm g (arr (arr a a) (arr a a))
test  = lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0)))))))
Ty1 : Type
Ty1 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty1 : Ty1
empty1 = \ _, empty, _ => empty

arr1 : Ty1 -> Ty1 -> Ty1
arr1 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con1 : Type
Con1 = (Con1 : Type)
 ->(nil  : Con1)
 ->(snoc : Con1 -> Ty1 -> Con1)
 -> Con1

nil1 : Con1
nil1 = \ con, nil1, snoc => nil1

snoc1 : Con1 -> Ty1 -> Con1
snoc1 = \ g, a, con, nil1, snoc1 => snoc1 (g con nil1 snoc1) a

Var1 : Con1 -> Ty1 -> Type
Var1 = \ g, a =>
    (Var1 : Con1 -> Ty1 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var1 (snoc1 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var1 g a -> Var1 (snoc1 g b) a)
 -> Var1 g a

vz1 : {g : _}-> {a : _} -> Var1 (snoc1 g a) a
vz1 = \ var, vz1, vs => vz1 _ _

vs1 : {g : _} -> {B : _} -> {a : _} -> Var1 g a -> Var1 (snoc1 g B) a
vs1 = \ x, var, vz1, vs1 => vs1 _ _ _ (x var vz1 vs1)

Tm1 : Con1 -> Ty1 -> Type
Tm1 = \ g, a =>
    (Tm1    : Con1 -> Ty1 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var1 g a -> Tm1 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm1 (snoc1 g a) B -> Tm1 g (arr1 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm1 g (arr1 a B) -> Tm1 g a -> Tm1 g B)
 -> Tm1 g a

var1 : {g : _} -> {a : _} -> Var1 g a -> Tm1 g a
var1 = \ x, tm, var1, lam, app => var1 _ _ x

lam1 : {g : _} -> {a : _} -> {B : _} -> Tm1 (snoc1 g a) B -> Tm1 g (arr1 a B)
lam1 = \ t, tm, var1, lam1, app => lam1 _ _ _ (t tm var1 lam1 app)

app1 : {g:_}->{a:_}->{B:_} -> Tm1 g (arr1 a B) -> Tm1 g a -> Tm1 g B
app1 = \ t, u, tm, var1, lam1, app1 => app1 _ _ _ (t tm var1 lam1 app1) (u tm var1 lam1 app1)

v01 : {g:_}->{a:_} -> Tm1 (snoc1 g a) a
v01 = var1 vz1

v11 : {g:_}->{a:_}-> {B:_}-> Tm1 (snoc1 (snoc1 g a) B) a
v11 = var1 (vs1 vz1)

v21 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm1 (snoc1 (snoc1 (snoc1 g a) B) C) a
v21 = var1 (vs1 (vs1 vz1))

v31 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm1 (snoc1 (snoc1 (snoc1 (snoc1 g a) B) C) D) a
v31 = var1 (vs1 (vs1 (vs1 vz1)))

v41 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm1 (snoc1 (snoc1 (snoc1 (snoc1 (snoc1 g a) B) C) D) E) a
v41 = var1 (vs1 (vs1 (vs1 (vs1 vz1))))

test1 : {g:_}-> {a:_} -> Tm1 g (arr1 (arr1 a a) (arr1 a a))
test1  = lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01)))))))
Ty2 : Type
Ty2 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty2 : Ty2
empty2 = \ _, empty, _ => empty

arr2 : Ty2 -> Ty2 -> Ty2
arr2 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con2 : Type
Con2 = (Con2 : Type)
 ->(nil  : Con2)
 ->(snoc : Con2 -> Ty2 -> Con2)
 -> Con2

nil2 : Con2
nil2 = \ con, nil2, snoc => nil2

snoc2 : Con2 -> Ty2 -> Con2
snoc2 = \ g, a, con, nil2, snoc2 => snoc2 (g con nil2 snoc2) a

Var2 : Con2 -> Ty2 -> Type
Var2 = \ g, a =>
    (Var2 : Con2 -> Ty2 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var2 (snoc2 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var2 g a -> Var2 (snoc2 g b) a)
 -> Var2 g a

vz2 : {g : _}-> {a : _} -> Var2 (snoc2 g a) a
vz2 = \ var, vz2, vs => vz2 _ _

vs2 : {g : _} -> {B : _} -> {a : _} -> Var2 g a -> Var2 (snoc2 g B) a
vs2 = \ x, var, vz2, vs2 => vs2 _ _ _ (x var vz2 vs2)

Tm2 : Con2 -> Ty2 -> Type
Tm2 = \ g, a =>
    (Tm2    : Con2 -> Ty2 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var2 g a -> Tm2 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm2 (snoc2 g a) B -> Tm2 g (arr2 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm2 g (arr2 a B) -> Tm2 g a -> Tm2 g B)
 -> Tm2 g a

var2 : {g : _} -> {a : _} -> Var2 g a -> Tm2 g a
var2 = \ x, tm, var2, lam, app => var2 _ _ x

lam2 : {g : _} -> {a : _} -> {B : _} -> Tm2 (snoc2 g a) B -> Tm2 g (arr2 a B)
lam2 = \ t, tm, var2, lam2, app => lam2 _ _ _ (t tm var2 lam2 app)

app2 : {g:_}->{a:_}->{B:_} -> Tm2 g (arr2 a B) -> Tm2 g a -> Tm2 g B
app2 = \ t, u, tm, var2, lam2, app2 => app2 _ _ _ (t tm var2 lam2 app2) (u tm var2 lam2 app2)

v02 : {g:_}->{a:_} -> Tm2 (snoc2 g a) a
v02 = var2 vz2

v12 : {g:_}->{a:_}-> {B:_}-> Tm2 (snoc2 (snoc2 g a) B) a
v12 = var2 (vs2 vz2)

v22 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm2 (snoc2 (snoc2 (snoc2 g a) B) C) a
v22 = var2 (vs2 (vs2 vz2))

v32 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm2 (snoc2 (snoc2 (snoc2 (snoc2 g a) B) C) D) a
v32 = var2 (vs2 (vs2 (vs2 vz2)))

v42 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm2 (snoc2 (snoc2 (snoc2 (snoc2 (snoc2 g a) B) C) D) E) a
v42 = var2 (vs2 (vs2 (vs2 (vs2 vz2))))

test2 : {g:_}-> {a:_} -> Tm2 g (arr2 (arr2 a a) (arr2 a a))
test2  = lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02)))))))
Ty3 : Type
Ty3 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty3 : Ty3
empty3 = \ _, empty, _ => empty

arr3 : Ty3 -> Ty3 -> Ty3
arr3 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con3 : Type
Con3 = (Con3 : Type)
 ->(nil  : Con3)
 ->(snoc : Con3 -> Ty3 -> Con3)
 -> Con3

nil3 : Con3
nil3 = \ con, nil3, snoc => nil3

snoc3 : Con3 -> Ty3 -> Con3
snoc3 = \ g, a, con, nil3, snoc3 => snoc3 (g con nil3 snoc3) a

Var3 : Con3 -> Ty3 -> Type
Var3 = \ g, a =>
    (Var3 : Con3 -> Ty3 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var3 (snoc3 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var3 g a -> Var3 (snoc3 g b) a)
 -> Var3 g a

vz3 : {g : _}-> {a : _} -> Var3 (snoc3 g a) a
vz3 = \ var, vz3, vs => vz3 _ _

vs3 : {g : _} -> {B : _} -> {a : _} -> Var3 g a -> Var3 (snoc3 g B) a
vs3 = \ x, var, vz3, vs3 => vs3 _ _ _ (x var vz3 vs3)

Tm3 : Con3 -> Ty3 -> Type
Tm3 = \ g, a =>
    (Tm3    : Con3 -> Ty3 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var3 g a -> Tm3 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm3 (snoc3 g a) B -> Tm3 g (arr3 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm3 g (arr3 a B) -> Tm3 g a -> Tm3 g B)
 -> Tm3 g a

var3 : {g : _} -> {a : _} -> Var3 g a -> Tm3 g a
var3 = \ x, tm, var3, lam, app => var3 _ _ x

lam3 : {g : _} -> {a : _} -> {B : _} -> Tm3 (snoc3 g a) B -> Tm3 g (arr3 a B)
lam3 = \ t, tm, var3, lam3, app => lam3 _ _ _ (t tm var3 lam3 app)

app3 : {g:_}->{a:_}->{B:_} -> Tm3 g (arr3 a B) -> Tm3 g a -> Tm3 g B
app3 = \ t, u, tm, var3, lam3, app3 => app3 _ _ _ (t tm var3 lam3 app3) (u tm var3 lam3 app3)

v03 : {g:_}->{a:_} -> Tm3 (snoc3 g a) a
v03 = var3 vz3

v13 : {g:_}->{a:_}-> {B:_}-> Tm3 (snoc3 (snoc3 g a) B) a
v13 = var3 (vs3 vz3)

v23 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm3 (snoc3 (snoc3 (snoc3 g a) B) C) a
v23 = var3 (vs3 (vs3 vz3))

v33 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm3 (snoc3 (snoc3 (snoc3 (snoc3 g a) B) C) D) a
v33 = var3 (vs3 (vs3 (vs3 vz3)))

v43 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm3 (snoc3 (snoc3 (snoc3 (snoc3 (snoc3 g a) B) C) D) E) a
v43 = var3 (vs3 (vs3 (vs3 (vs3 vz3))))

test3 : {g:_}-> {a:_} -> Tm3 g (arr3 (arr3 a a) (arr3 a a))
test3  = lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03)))))))
Ty4 : Type
Ty4 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty4 : Ty4
empty4 = \ _, empty, _ => empty

arr4 : Ty4 -> Ty4 -> Ty4
arr4 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con4 : Type
Con4 = (Con4 : Type)
 ->(nil  : Con4)
 ->(snoc : Con4 -> Ty4 -> Con4)
 -> Con4

nil4 : Con4
nil4 = \ con, nil4, snoc => nil4

snoc4 : Con4 -> Ty4 -> Con4
snoc4 = \ g, a, con, nil4, snoc4 => snoc4 (g con nil4 snoc4) a

Var4 : Con4 -> Ty4 -> Type
Var4 = \ g, a =>
    (Var4 : Con4 -> Ty4 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var4 (snoc4 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var4 g a -> Var4 (snoc4 g b) a)
 -> Var4 g a

vz4 : {g : _}-> {a : _} -> Var4 (snoc4 g a) a
vz4 = \ var, vz4, vs => vz4 _ _

vs4 : {g : _} -> {B : _} -> {a : _} -> Var4 g a -> Var4 (snoc4 g B) a
vs4 = \ x, var, vz4, vs4 => vs4 _ _ _ (x var vz4 vs4)

Tm4 : Con4 -> Ty4 -> Type
Tm4 = \ g, a =>
    (Tm4    : Con4 -> Ty4 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var4 g a -> Tm4 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm4 (snoc4 g a) B -> Tm4 g (arr4 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm4 g (arr4 a B) -> Tm4 g a -> Tm4 g B)
 -> Tm4 g a

var4 : {g : _} -> {a : _} -> Var4 g a -> Tm4 g a
var4 = \ x, tm, var4, lam, app => var4 _ _ x

lam4 : {g : _} -> {a : _} -> {B : _} -> Tm4 (snoc4 g a) B -> Tm4 g (arr4 a B)
lam4 = \ t, tm, var4, lam4, app => lam4 _ _ _ (t tm var4 lam4 app)

app4 : {g:_}->{a:_}->{B:_} -> Tm4 g (arr4 a B) -> Tm4 g a -> Tm4 g B
app4 = \ t, u, tm, var4, lam4, app4 => app4 _ _ _ (t tm var4 lam4 app4) (u tm var4 lam4 app4)

v04 : {g:_}->{a:_} -> Tm4 (snoc4 g a) a
v04 = var4 vz4

v14 : {g:_}->{a:_}-> {B:_}-> Tm4 (snoc4 (snoc4 g a) B) a
v14 = var4 (vs4 vz4)

v24 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm4 (snoc4 (snoc4 (snoc4 g a) B) C) a
v24 = var4 (vs4 (vs4 vz4))

v34 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm4 (snoc4 (snoc4 (snoc4 (snoc4 g a) B) C) D) a
v34 = var4 (vs4 (vs4 (vs4 vz4)))

v44 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm4 (snoc4 (snoc4 (snoc4 (snoc4 (snoc4 g a) B) C) D) E) a
v44 = var4 (vs4 (vs4 (vs4 (vs4 vz4))))

test4 : {g:_}-> {a:_} -> Tm4 g (arr4 (arr4 a a) (arr4 a a))
test4  = lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04)))))))
Ty5 : Type
Ty5 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty5 : Ty5
empty5 = \ _, empty, _ => empty

arr5 : Ty5 -> Ty5 -> Ty5
arr5 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con5 : Type
Con5 = (Con5 : Type)
 ->(nil  : Con5)
 ->(snoc : Con5 -> Ty5 -> Con5)
 -> Con5

nil5 : Con5
nil5 = \ con, nil5, snoc => nil5

snoc5 : Con5 -> Ty5 -> Con5
snoc5 = \ g, a, con, nil5, snoc5 => snoc5 (g con nil5 snoc5) a

Var5 : Con5 -> Ty5 -> Type
Var5 = \ g, a =>
    (Var5 : Con5 -> Ty5 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var5 (snoc5 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var5 g a -> Var5 (snoc5 g b) a)
 -> Var5 g a

vz5 : {g : _}-> {a : _} -> Var5 (snoc5 g a) a
vz5 = \ var, vz5, vs => vz5 _ _

vs5 : {g : _} -> {B : _} -> {a : _} -> Var5 g a -> Var5 (snoc5 g B) a
vs5 = \ x, var, vz5, vs5 => vs5 _ _ _ (x var vz5 vs5)

Tm5 : Con5 -> Ty5 -> Type
Tm5 = \ g, a =>
    (Tm5    : Con5 -> Ty5 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var5 g a -> Tm5 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm5 (snoc5 g a) B -> Tm5 g (arr5 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm5 g (arr5 a B) -> Tm5 g a -> Tm5 g B)
 -> Tm5 g a

var5 : {g : _} -> {a : _} -> Var5 g a -> Tm5 g a
var5 = \ x, tm, var5, lam, app => var5 _ _ x

lam5 : {g : _} -> {a : _} -> {B : _} -> Tm5 (snoc5 g a) B -> Tm5 g (arr5 a B)
lam5 = \ t, tm, var5, lam5, app => lam5 _ _ _ (t tm var5 lam5 app)

app5 : {g:_}->{a:_}->{B:_} -> Tm5 g (arr5 a B) -> Tm5 g a -> Tm5 g B
app5 = \ t, u, tm, var5, lam5, app5 => app5 _ _ _ (t tm var5 lam5 app5) (u tm var5 lam5 app5)

v05 : {g:_}->{a:_} -> Tm5 (snoc5 g a) a
v05 = var5 vz5

v15 : {g:_}->{a:_}-> {B:_}-> Tm5 (snoc5 (snoc5 g a) B) a
v15 = var5 (vs5 vz5)

v25 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm5 (snoc5 (snoc5 (snoc5 g a) B) C) a
v25 = var5 (vs5 (vs5 vz5))

v35 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm5 (snoc5 (snoc5 (snoc5 (snoc5 g a) B) C) D) a
v35 = var5 (vs5 (vs5 (vs5 vz5)))

v45 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm5 (snoc5 (snoc5 (snoc5 (snoc5 (snoc5 g a) B) C) D) E) a
v45 = var5 (vs5 (vs5 (vs5 (vs5 vz5))))

test5 : {g:_}-> {a:_} -> Tm5 g (arr5 (arr5 a a) (arr5 a a))
test5  = lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05)))))))
Ty6 : Type
Ty6 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty6 : Ty6
empty6 = \ _, empty, _ => empty

arr6 : Ty6 -> Ty6 -> Ty6
arr6 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con6 : Type
Con6 = (Con6 : Type)
 ->(nil  : Con6)
 ->(snoc : Con6 -> Ty6 -> Con6)
 -> Con6

nil6 : Con6
nil6 = \ con, nil6, snoc => nil6

snoc6 : Con6 -> Ty6 -> Con6
snoc6 = \ g, a, con, nil6, snoc6 => snoc6 (g con nil6 snoc6) a

Var6 : Con6 -> Ty6 -> Type
Var6 = \ g, a =>
    (Var6 : Con6 -> Ty6 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var6 (snoc6 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var6 g a -> Var6 (snoc6 g b) a)
 -> Var6 g a

vz6 : {g : _}-> {a : _} -> Var6 (snoc6 g a) a
vz6 = \ var, vz6, vs => vz6 _ _

vs6 : {g : _} -> {B : _} -> {a : _} -> Var6 g a -> Var6 (snoc6 g B) a
vs6 = \ x, var, vz6, vs6 => vs6 _ _ _ (x var vz6 vs6)

Tm6 : Con6 -> Ty6 -> Type
Tm6 = \ g, a =>
    (Tm6    : Con6 -> Ty6 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var6 g a -> Tm6 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm6 (snoc6 g a) B -> Tm6 g (arr6 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm6 g (arr6 a B) -> Tm6 g a -> Tm6 g B)
 -> Tm6 g a

var6 : {g : _} -> {a : _} -> Var6 g a -> Tm6 g a
var6 = \ x, tm, var6, lam, app => var6 _ _ x

lam6 : {g : _} -> {a : _} -> {B : _} -> Tm6 (snoc6 g a) B -> Tm6 g (arr6 a B)
lam6 = \ t, tm, var6, lam6, app => lam6 _ _ _ (t tm var6 lam6 app)

app6 : {g:_}->{a:_}->{B:_} -> Tm6 g (arr6 a B) -> Tm6 g a -> Tm6 g B
app6 = \ t, u, tm, var6, lam6, app6 => app6 _ _ _ (t tm var6 lam6 app6) (u tm var6 lam6 app6)

v06 : {g:_}->{a:_} -> Tm6 (snoc6 g a) a
v06 = var6 vz6

v16 : {g:_}->{a:_}-> {B:_}-> Tm6 (snoc6 (snoc6 g a) B) a
v16 = var6 (vs6 vz6)

v26 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm6 (snoc6 (snoc6 (snoc6 g a) B) C) a
v26 = var6 (vs6 (vs6 vz6))

v36 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm6 (snoc6 (snoc6 (snoc6 (snoc6 g a) B) C) D) a
v36 = var6 (vs6 (vs6 (vs6 vz6)))

v46 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm6 (snoc6 (snoc6 (snoc6 (snoc6 (snoc6 g a) B) C) D) E) a
v46 = var6 (vs6 (vs6 (vs6 (vs6 vz6))))

test6 : {g:_}-> {a:_} -> Tm6 g (arr6 (arr6 a a) (arr6 a a))
test6  = lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06)))))))
Ty7 : Type
Ty7 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty7 : Ty7
empty7 = \ _, empty, _ => empty

arr7 : Ty7 -> Ty7 -> Ty7
arr7 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con7 : Type
Con7 = (Con7 : Type)
 ->(nil  : Con7)
 ->(snoc : Con7 -> Ty7 -> Con7)
 -> Con7

nil7 : Con7
nil7 = \ con, nil7, snoc => nil7

snoc7 : Con7 -> Ty7 -> Con7
snoc7 = \ g, a, con, nil7, snoc7 => snoc7 (g con nil7 snoc7) a

Var7 : Con7 -> Ty7 -> Type
Var7 = \ g, a =>
    (Var7 : Con7 -> Ty7 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var7 (snoc7 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var7 g a -> Var7 (snoc7 g b) a)
 -> Var7 g a

vz7 : {g : _}-> {a : _} -> Var7 (snoc7 g a) a
vz7 = \ var, vz7, vs => vz7 _ _

vs7 : {g : _} -> {B : _} -> {a : _} -> Var7 g a -> Var7 (snoc7 g B) a
vs7 = \ x, var, vz7, vs7 => vs7 _ _ _ (x var vz7 vs7)

Tm7 : Con7 -> Ty7 -> Type
Tm7 = \ g, a =>
    (Tm7    : Con7 -> Ty7 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var7 g a -> Tm7 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm7 (snoc7 g a) B -> Tm7 g (arr7 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm7 g (arr7 a B) -> Tm7 g a -> Tm7 g B)
 -> Tm7 g a

var7 : {g : _} -> {a : _} -> Var7 g a -> Tm7 g a
var7 = \ x, tm, var7, lam, app => var7 _ _ x

lam7 : {g : _} -> {a : _} -> {B : _} -> Tm7 (snoc7 g a) B -> Tm7 g (arr7 a B)
lam7 = \ t, tm, var7, lam7, app => lam7 _ _ _ (t tm var7 lam7 app)

app7 : {g:_}->{a:_}->{B:_} -> Tm7 g (arr7 a B) -> Tm7 g a -> Tm7 g B
app7 = \ t, u, tm, var7, lam7, app7 => app7 _ _ _ (t tm var7 lam7 app7) (u tm var7 lam7 app7)

v07 : {g:_}->{a:_} -> Tm7 (snoc7 g a) a
v07 = var7 vz7

v17 : {g:_}->{a:_}-> {B:_}-> Tm7 (snoc7 (snoc7 g a) B) a
v17 = var7 (vs7 vz7)

v27 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm7 (snoc7 (snoc7 (snoc7 g a) B) C) a
v27 = var7 (vs7 (vs7 vz7))

v37 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm7 (snoc7 (snoc7 (snoc7 (snoc7 g a) B) C) D) a
v37 = var7 (vs7 (vs7 (vs7 vz7)))

v47 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm7 (snoc7 (snoc7 (snoc7 (snoc7 (snoc7 g a) B) C) D) E) a
v47 = var7 (vs7 (vs7 (vs7 (vs7 vz7))))

test7 : {g:_}-> {a:_} -> Tm7 g (arr7 (arr7 a a) (arr7 a a))
test7  = lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07)))))))
Ty8 : Type
Ty8 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty8 : Ty8
empty8 = \ _, empty, _ => empty

arr8 : Ty8 -> Ty8 -> Ty8
arr8 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con8 : Type
Con8 = (Con8 : Type)
 ->(nil  : Con8)
 ->(snoc : Con8 -> Ty8 -> Con8)
 -> Con8

nil8 : Con8
nil8 = \ con, nil8, snoc => nil8

snoc8 : Con8 -> Ty8 -> Con8
snoc8 = \ g, a, con, nil8, snoc8 => snoc8 (g con nil8 snoc8) a

Var8 : Con8 -> Ty8 -> Type
Var8 = \ g, a =>
    (Var8 : Con8 -> Ty8 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var8 (snoc8 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var8 g a -> Var8 (snoc8 g b) a)
 -> Var8 g a

vz8 : {g : _}-> {a : _} -> Var8 (snoc8 g a) a
vz8 = \ var, vz8, vs => vz8 _ _

vs8 : {g : _} -> {B : _} -> {a : _} -> Var8 g a -> Var8 (snoc8 g B) a
vs8 = \ x, var, vz8, vs8 => vs8 _ _ _ (x var vz8 vs8)

Tm8 : Con8 -> Ty8 -> Type
Tm8 = \ g, a =>
    (Tm8    : Con8 -> Ty8 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var8 g a -> Tm8 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm8 (snoc8 g a) B -> Tm8 g (arr8 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm8 g (arr8 a B) -> Tm8 g a -> Tm8 g B)
 -> Tm8 g a

var8 : {g : _} -> {a : _} -> Var8 g a -> Tm8 g a
var8 = \ x, tm, var8, lam, app => var8 _ _ x

lam8 : {g : _} -> {a : _} -> {B : _} -> Tm8 (snoc8 g a) B -> Tm8 g (arr8 a B)
lam8 = \ t, tm, var8, lam8, app => lam8 _ _ _ (t tm var8 lam8 app)

app8 : {g:_}->{a:_}->{B:_} -> Tm8 g (arr8 a B) -> Tm8 g a -> Tm8 g B
app8 = \ t, u, tm, var8, lam8, app8 => app8 _ _ _ (t tm var8 lam8 app8) (u tm var8 lam8 app8)

v08 : {g:_}->{a:_} -> Tm8 (snoc8 g a) a
v08 = var8 vz8

v18 : {g:_}->{a:_}-> {B:_}-> Tm8 (snoc8 (snoc8 g a) B) a
v18 = var8 (vs8 vz8)

v28 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm8 (snoc8 (snoc8 (snoc8 g a) B) C) a
v28 = var8 (vs8 (vs8 vz8))

v38 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm8 (snoc8 (snoc8 (snoc8 (snoc8 g a) B) C) D) a
v38 = var8 (vs8 (vs8 (vs8 vz8)))

v48 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm8 (snoc8 (snoc8 (snoc8 (snoc8 (snoc8 g a) B) C) D) E) a
v48 = var8 (vs8 (vs8 (vs8 (vs8 vz8))))

test8 : {g:_}-> {a:_} -> Tm8 g (arr8 (arr8 a a) (arr8 a a))
test8  = lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08)))))))
Ty9 : Type
Ty9 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty9 : Ty9
empty9 = \ _, empty, _ => empty

arr9 : Ty9 -> Ty9 -> Ty9
arr9 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con9 : Type
Con9 = (Con9 : Type)
 ->(nil  : Con9)
 ->(snoc : Con9 -> Ty9 -> Con9)
 -> Con9

nil9 : Con9
nil9 = \ con, nil9, snoc => nil9

snoc9 : Con9 -> Ty9 -> Con9
snoc9 = \ g, a, con, nil9, snoc9 => snoc9 (g con nil9 snoc9) a

Var9 : Con9 -> Ty9 -> Type
Var9 = \ g, a =>
    (Var9 : Con9 -> Ty9 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var9 (snoc9 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var9 g a -> Var9 (snoc9 g b) a)
 -> Var9 g a

vz9 : {g : _}-> {a : _} -> Var9 (snoc9 g a) a
vz9 = \ var, vz9, vs => vz9 _ _

vs9 : {g : _} -> {B : _} -> {a : _} -> Var9 g a -> Var9 (snoc9 g B) a
vs9 = \ x, var, vz9, vs9 => vs9 _ _ _ (x var vz9 vs9)

Tm9 : Con9 -> Ty9 -> Type
Tm9 = \ g, a =>
    (Tm9    : Con9 -> Ty9 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var9 g a -> Tm9 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm9 (snoc9 g a) B -> Tm9 g (arr9 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm9 g (arr9 a B) -> Tm9 g a -> Tm9 g B)
 -> Tm9 g a

var9 : {g : _} -> {a : _} -> Var9 g a -> Tm9 g a
var9 = \ x, tm, var9, lam, app => var9 _ _ x

lam9 : {g : _} -> {a : _} -> {B : _} -> Tm9 (snoc9 g a) B -> Tm9 g (arr9 a B)
lam9 = \ t, tm, var9, lam9, app => lam9 _ _ _ (t tm var9 lam9 app)

app9 : {g:_}->{a:_}->{B:_} -> Tm9 g (arr9 a B) -> Tm9 g a -> Tm9 g B
app9 = \ t, u, tm, var9, lam9, app9 => app9 _ _ _ (t tm var9 lam9 app9) (u tm var9 lam9 app9)

v09 : {g:_}->{a:_} -> Tm9 (snoc9 g a) a
v09 = var9 vz9

v19 : {g:_}->{a:_}-> {B:_}-> Tm9 (snoc9 (snoc9 g a) B) a
v19 = var9 (vs9 vz9)

v29 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm9 (snoc9 (snoc9 (snoc9 g a) B) C) a
v29 = var9 (vs9 (vs9 vz9))

v39 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm9 (snoc9 (snoc9 (snoc9 (snoc9 g a) B) C) D) a
v39 = var9 (vs9 (vs9 (vs9 vz9)))

v49 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm9 (snoc9 (snoc9 (snoc9 (snoc9 (snoc9 g a) B) C) D) E) a
v49 = var9 (vs9 (vs9 (vs9 (vs9 vz9))))

test9 : {g:_}-> {a:_} -> Tm9 g (arr9 (arr9 a a) (arr9 a a))
test9  = lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09)))))))
Ty10 : Type
Ty10 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty10 : Ty10
empty10 = \ _, empty, _ => empty

arr10 : Ty10 -> Ty10 -> Ty10
arr10 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con10 : Type
Con10 = (Con10 : Type)
 ->(nil  : Con10)
 ->(snoc : Con10 -> Ty10 -> Con10)
 -> Con10

nil10 : Con10
nil10 = \ con, nil10, snoc => nil10

snoc10 : Con10 -> Ty10 -> Con10
snoc10 = \ g, a, con, nil10, snoc10 => snoc10 (g con nil10 snoc10) a

Var10 : Con10 -> Ty10 -> Type
Var10 = \ g, a =>
    (Var10 : Con10 -> Ty10 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var10 (snoc10 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var10 g a -> Var10 (snoc10 g b) a)
 -> Var10 g a

vz10 : {g : _}-> {a : _} -> Var10 (snoc10 g a) a
vz10 = \ var, vz10, vs => vz10 _ _

vs10 : {g : _} -> {B : _} -> {a : _} -> Var10 g a -> Var10 (snoc10 g B) a
vs10 = \ x, var, vz10, vs10 => vs10 _ _ _ (x var vz10 vs10)

Tm10 : Con10 -> Ty10 -> Type
Tm10 = \ g, a =>
    (Tm10    : Con10 -> Ty10 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var10 g a -> Tm10 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm10 (snoc10 g a) B -> Tm10 g (arr10 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm10 g (arr10 a B) -> Tm10 g a -> Tm10 g B)
 -> Tm10 g a

var10 : {g : _} -> {a : _} -> Var10 g a -> Tm10 g a
var10 = \ x, tm, var10, lam, app => var10 _ _ x

lam10 : {g : _} -> {a : _} -> {B : _} -> Tm10 (snoc10 g a) B -> Tm10 g (arr10 a B)
lam10 = \ t, tm, var10, lam10, app => lam10 _ _ _ (t tm var10 lam10 app)

app10 : {g:_}->{a:_}->{B:_} -> Tm10 g (arr10 a B) -> Tm10 g a -> Tm10 g B
app10 = \ t, u, tm, var10, lam10, app10 => app10 _ _ _ (t tm var10 lam10 app10) (u tm var10 lam10 app10)

v010 : {g:_}->{a:_} -> Tm10 (snoc10 g a) a
v010 = var10 vz10

v110 : {g:_}->{a:_}-> {B:_}-> Tm10 (snoc10 (snoc10 g a) B) a
v110 = var10 (vs10 vz10)

v210 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm10 (snoc10 (snoc10 (snoc10 g a) B) C) a
v210 = var10 (vs10 (vs10 vz10))

v310 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm10 (snoc10 (snoc10 (snoc10 (snoc10 g a) B) C) D) a
v310 = var10 (vs10 (vs10 (vs10 vz10)))

v410 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm10 (snoc10 (snoc10 (snoc10 (snoc10 (snoc10 g a) B) C) D) E) a
v410 = var10 (vs10 (vs10 (vs10 (vs10 vz10))))

test10 : {g:_}-> {a:_} -> Tm10 g (arr10 (arr10 a a) (arr10 a a))
test10  = lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010)))))))
Ty11 : Type
Ty11 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty11 : Ty11
empty11 = \ _, empty, _ => empty

arr11 : Ty11 -> Ty11 -> Ty11
arr11 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con11 : Type
Con11 = (Con11 : Type)
 ->(nil  : Con11)
 ->(snoc : Con11 -> Ty11 -> Con11)
 -> Con11

nil11 : Con11
nil11 = \ con, nil11, snoc => nil11

snoc11 : Con11 -> Ty11 -> Con11
snoc11 = \ g, a, con, nil11, snoc11 => snoc11 (g con nil11 snoc11) a

Var11 : Con11 -> Ty11 -> Type
Var11 = \ g, a =>
    (Var11 : Con11 -> Ty11 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var11 (snoc11 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var11 g a -> Var11 (snoc11 g b) a)
 -> Var11 g a

vz11 : {g : _}-> {a : _} -> Var11 (snoc11 g a) a
vz11 = \ var, vz11, vs => vz11 _ _

vs11 : {g : _} -> {B : _} -> {a : _} -> Var11 g a -> Var11 (snoc11 g B) a
vs11 = \ x, var, vz11, vs11 => vs11 _ _ _ (x var vz11 vs11)

Tm11 : Con11 -> Ty11 -> Type
Tm11 = \ g, a =>
    (Tm11    : Con11 -> Ty11 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var11 g a -> Tm11 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm11 (snoc11 g a) B -> Tm11 g (arr11 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm11 g (arr11 a B) -> Tm11 g a -> Tm11 g B)
 -> Tm11 g a

var11 : {g : _} -> {a : _} -> Var11 g a -> Tm11 g a
var11 = \ x, tm, var11, lam, app => var11 _ _ x

lam11 : {g : _} -> {a : _} -> {B : _} -> Tm11 (snoc11 g a) B -> Tm11 g (arr11 a B)
lam11 = \ t, tm, var11, lam11, app => lam11 _ _ _ (t tm var11 lam11 app)

app11 : {g:_}->{a:_}->{B:_} -> Tm11 g (arr11 a B) -> Tm11 g a -> Tm11 g B
app11 = \ t, u, tm, var11, lam11, app11 => app11 _ _ _ (t tm var11 lam11 app11) (u tm var11 lam11 app11)

v011 : {g:_}->{a:_} -> Tm11 (snoc11 g a) a
v011 = var11 vz11

v111 : {g:_}->{a:_}-> {B:_}-> Tm11 (snoc11 (snoc11 g a) B) a
v111 = var11 (vs11 vz11)

v211 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm11 (snoc11 (snoc11 (snoc11 g a) B) C) a
v211 = var11 (vs11 (vs11 vz11))

v311 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm11 (snoc11 (snoc11 (snoc11 (snoc11 g a) B) C) D) a
v311 = var11 (vs11 (vs11 (vs11 vz11)))

v411 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm11 (snoc11 (snoc11 (snoc11 (snoc11 (snoc11 g a) B) C) D) E) a
v411 = var11 (vs11 (vs11 (vs11 (vs11 vz11))))

test11 : {g:_}-> {a:_} -> Tm11 g (arr11 (arr11 a a) (arr11 a a))
test11  = lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011)))))))
Ty12 : Type
Ty12 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty12 : Ty12
empty12 = \ _, empty, _ => empty

arr12 : Ty12 -> Ty12 -> Ty12
arr12 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con12 : Type
Con12 = (Con12 : Type)
 ->(nil  : Con12)
 ->(snoc : Con12 -> Ty12 -> Con12)
 -> Con12

nil12 : Con12
nil12 = \ con, nil12, snoc => nil12

snoc12 : Con12 -> Ty12 -> Con12
snoc12 = \ g, a, con, nil12, snoc12 => snoc12 (g con nil12 snoc12) a

Var12 : Con12 -> Ty12 -> Type
Var12 = \ g, a =>
    (Var12 : Con12 -> Ty12 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var12 (snoc12 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var12 g a -> Var12 (snoc12 g b) a)
 -> Var12 g a

vz12 : {g : _}-> {a : _} -> Var12 (snoc12 g a) a
vz12 = \ var, vz12, vs => vz12 _ _

vs12 : {g : _} -> {B : _} -> {a : _} -> Var12 g a -> Var12 (snoc12 g B) a
vs12 = \ x, var, vz12, vs12 => vs12 _ _ _ (x var vz12 vs12)

Tm12 : Con12 -> Ty12 -> Type
Tm12 = \ g, a =>
    (Tm12    : Con12 -> Ty12 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var12 g a -> Tm12 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm12 (snoc12 g a) B -> Tm12 g (arr12 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm12 g (arr12 a B) -> Tm12 g a -> Tm12 g B)
 -> Tm12 g a

var12 : {g : _} -> {a : _} -> Var12 g a -> Tm12 g a
var12 = \ x, tm, var12, lam, app => var12 _ _ x

lam12 : {g : _} -> {a : _} -> {B : _} -> Tm12 (snoc12 g a) B -> Tm12 g (arr12 a B)
lam12 = \ t, tm, var12, lam12, app => lam12 _ _ _ (t tm var12 lam12 app)

app12 : {g:_}->{a:_}->{B:_} -> Tm12 g (arr12 a B) -> Tm12 g a -> Tm12 g B
app12 = \ t, u, tm, var12, lam12, app12 => app12 _ _ _ (t tm var12 lam12 app12) (u tm var12 lam12 app12)

v012 : {g:_}->{a:_} -> Tm12 (snoc12 g a) a
v012 = var12 vz12

v112 : {g:_}->{a:_}-> {B:_}-> Tm12 (snoc12 (snoc12 g a) B) a
v112 = var12 (vs12 vz12)

v212 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm12 (snoc12 (snoc12 (snoc12 g a) B) C) a
v212 = var12 (vs12 (vs12 vz12))

v312 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm12 (snoc12 (snoc12 (snoc12 (snoc12 g a) B) C) D) a
v312 = var12 (vs12 (vs12 (vs12 vz12)))

v412 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm12 (snoc12 (snoc12 (snoc12 (snoc12 (snoc12 g a) B) C) D) E) a
v412 = var12 (vs12 (vs12 (vs12 (vs12 vz12))))

test12 : {g:_}-> {a:_} -> Tm12 g (arr12 (arr12 a a) (arr12 a a))
test12  = lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012)))))))
Ty13 : Type
Ty13 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty13 : Ty13
empty13 = \ _, empty, _ => empty

arr13 : Ty13 -> Ty13 -> Ty13
arr13 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con13 : Type
Con13 = (Con13 : Type)
 ->(nil  : Con13)
 ->(snoc : Con13 -> Ty13 -> Con13)
 -> Con13

nil13 : Con13
nil13 = \ con, nil13, snoc => nil13

snoc13 : Con13 -> Ty13 -> Con13
snoc13 = \ g, a, con, nil13, snoc13 => snoc13 (g con nil13 snoc13) a

Var13 : Con13 -> Ty13 -> Type
Var13 = \ g, a =>
    (Var13 : Con13 -> Ty13 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var13 (snoc13 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var13 g a -> Var13 (snoc13 g b) a)
 -> Var13 g a

vz13 : {g : _}-> {a : _} -> Var13 (snoc13 g a) a
vz13 = \ var, vz13, vs => vz13 _ _

vs13 : {g : _} -> {B : _} -> {a : _} -> Var13 g a -> Var13 (snoc13 g B) a
vs13 = \ x, var, vz13, vs13 => vs13 _ _ _ (x var vz13 vs13)

Tm13 : Con13 -> Ty13 -> Type
Tm13 = \ g, a =>
    (Tm13    : Con13 -> Ty13 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var13 g a -> Tm13 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm13 (snoc13 g a) B -> Tm13 g (arr13 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm13 g (arr13 a B) -> Tm13 g a -> Tm13 g B)
 -> Tm13 g a

var13 : {g : _} -> {a : _} -> Var13 g a -> Tm13 g a
var13 = \ x, tm, var13, lam, app => var13 _ _ x

lam13 : {g : _} -> {a : _} -> {B : _} -> Tm13 (snoc13 g a) B -> Tm13 g (arr13 a B)
lam13 = \ t, tm, var13, lam13, app => lam13 _ _ _ (t tm var13 lam13 app)

app13 : {g:_}->{a:_}->{B:_} -> Tm13 g (arr13 a B) -> Tm13 g a -> Tm13 g B
app13 = \ t, u, tm, var13, lam13, app13 => app13 _ _ _ (t tm var13 lam13 app13) (u tm var13 lam13 app13)

v013 : {g:_}->{a:_} -> Tm13 (snoc13 g a) a
v013 = var13 vz13

v113 : {g:_}->{a:_}-> {B:_}-> Tm13 (snoc13 (snoc13 g a) B) a
v113 = var13 (vs13 vz13)

v213 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm13 (snoc13 (snoc13 (snoc13 g a) B) C) a
v213 = var13 (vs13 (vs13 vz13))

v313 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm13 (snoc13 (snoc13 (snoc13 (snoc13 g a) B) C) D) a
v313 = var13 (vs13 (vs13 (vs13 vz13)))

v413 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm13 (snoc13 (snoc13 (snoc13 (snoc13 (snoc13 g a) B) C) D) E) a
v413 = var13 (vs13 (vs13 (vs13 (vs13 vz13))))

test13 : {g:_}-> {a:_} -> Tm13 g (arr13 (arr13 a a) (arr13 a a))
test13  = lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013)))))))
Ty14 : Type
Ty14 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty14 : Ty14
empty14 = \ _, empty, _ => empty

arr14 : Ty14 -> Ty14 -> Ty14
arr14 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con14 : Type
Con14 = (Con14 : Type)
 ->(nil  : Con14)
 ->(snoc : Con14 -> Ty14 -> Con14)
 -> Con14

nil14 : Con14
nil14 = \ con, nil14, snoc => nil14

snoc14 : Con14 -> Ty14 -> Con14
snoc14 = \ g, a, con, nil14, snoc14 => snoc14 (g con nil14 snoc14) a

Var14 : Con14 -> Ty14 -> Type
Var14 = \ g, a =>
    (Var14 : Con14 -> Ty14 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var14 (snoc14 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var14 g a -> Var14 (snoc14 g b) a)
 -> Var14 g a

vz14 : {g : _}-> {a : _} -> Var14 (snoc14 g a) a
vz14 = \ var, vz14, vs => vz14 _ _

vs14 : {g : _} -> {B : _} -> {a : _} -> Var14 g a -> Var14 (snoc14 g B) a
vs14 = \ x, var, vz14, vs14 => vs14 _ _ _ (x var vz14 vs14)

Tm14 : Con14 -> Ty14 -> Type
Tm14 = \ g, a =>
    (Tm14    : Con14 -> Ty14 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var14 g a -> Tm14 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm14 (snoc14 g a) B -> Tm14 g (arr14 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm14 g (arr14 a B) -> Tm14 g a -> Tm14 g B)
 -> Tm14 g a

var14 : {g : _} -> {a : _} -> Var14 g a -> Tm14 g a
var14 = \ x, tm, var14, lam, app => var14 _ _ x

lam14 : {g : _} -> {a : _} -> {B : _} -> Tm14 (snoc14 g a) B -> Tm14 g (arr14 a B)
lam14 = \ t, tm, var14, lam14, app => lam14 _ _ _ (t tm var14 lam14 app)

app14 : {g:_}->{a:_}->{B:_} -> Tm14 g (arr14 a B) -> Tm14 g a -> Tm14 g B
app14 = \ t, u, tm, var14, lam14, app14 => app14 _ _ _ (t tm var14 lam14 app14) (u tm var14 lam14 app14)

v014 : {g:_}->{a:_} -> Tm14 (snoc14 g a) a
v014 = var14 vz14

v114 : {g:_}->{a:_}-> {B:_}-> Tm14 (snoc14 (snoc14 g a) B) a
v114 = var14 (vs14 vz14)

v214 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm14 (snoc14 (snoc14 (snoc14 g a) B) C) a
v214 = var14 (vs14 (vs14 vz14))

v314 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm14 (snoc14 (snoc14 (snoc14 (snoc14 g a) B) C) D) a
v314 = var14 (vs14 (vs14 (vs14 vz14)))

v414 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm14 (snoc14 (snoc14 (snoc14 (snoc14 (snoc14 g a) B) C) D) E) a
v414 = var14 (vs14 (vs14 (vs14 (vs14 vz14))))

test14 : {g:_}-> {a:_} -> Tm14 g (arr14 (arr14 a a) (arr14 a a))
test14  = lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014)))))))
Ty15 : Type
Ty15 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty15 : Ty15
empty15 = \ _, empty, _ => empty

arr15 : Ty15 -> Ty15 -> Ty15
arr15 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con15 : Type
Con15 = (Con15 : Type)
 ->(nil  : Con15)
 ->(snoc : Con15 -> Ty15 -> Con15)
 -> Con15

nil15 : Con15
nil15 = \ con, nil15, snoc => nil15

snoc15 : Con15 -> Ty15 -> Con15
snoc15 = \ g, a, con, nil15, snoc15 => snoc15 (g con nil15 snoc15) a

Var15 : Con15 -> Ty15 -> Type
Var15 = \ g, a =>
    (Var15 : Con15 -> Ty15 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var15 (snoc15 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var15 g a -> Var15 (snoc15 g b) a)
 -> Var15 g a

vz15 : {g : _}-> {a : _} -> Var15 (snoc15 g a) a
vz15 = \ var, vz15, vs => vz15 _ _

vs15 : {g : _} -> {B : _} -> {a : _} -> Var15 g a -> Var15 (snoc15 g B) a
vs15 = \ x, var, vz15, vs15 => vs15 _ _ _ (x var vz15 vs15)

Tm15 : Con15 -> Ty15 -> Type
Tm15 = \ g, a =>
    (Tm15    : Con15 -> Ty15 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var15 g a -> Tm15 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm15 (snoc15 g a) B -> Tm15 g (arr15 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm15 g (arr15 a B) -> Tm15 g a -> Tm15 g B)
 -> Tm15 g a

var15 : {g : _} -> {a : _} -> Var15 g a -> Tm15 g a
var15 = \ x, tm, var15, lam, app => var15 _ _ x

lam15 : {g : _} -> {a : _} -> {B : _} -> Tm15 (snoc15 g a) B -> Tm15 g (arr15 a B)
lam15 = \ t, tm, var15, lam15, app => lam15 _ _ _ (t tm var15 lam15 app)

app15 : {g:_}->{a:_}->{B:_} -> Tm15 g (arr15 a B) -> Tm15 g a -> Tm15 g B
app15 = \ t, u, tm, var15, lam15, app15 => app15 _ _ _ (t tm var15 lam15 app15) (u tm var15 lam15 app15)

v015 : {g:_}->{a:_} -> Tm15 (snoc15 g a) a
v015 = var15 vz15

v115 : {g:_}->{a:_}-> {B:_}-> Tm15 (snoc15 (snoc15 g a) B) a
v115 = var15 (vs15 vz15)

v215 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm15 (snoc15 (snoc15 (snoc15 g a) B) C) a
v215 = var15 (vs15 (vs15 vz15))

v315 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm15 (snoc15 (snoc15 (snoc15 (snoc15 g a) B) C) D) a
v315 = var15 (vs15 (vs15 (vs15 vz15)))

v415 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm15 (snoc15 (snoc15 (snoc15 (snoc15 (snoc15 g a) B) C) D) E) a
v415 = var15 (vs15 (vs15 (vs15 (vs15 vz15))))

test15 : {g:_}-> {a:_} -> Tm15 g (arr15 (arr15 a a) (arr15 a a))
test15  = lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015)))))))
Ty16 : Type
Ty16 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty16 : Ty16
empty16 = \ _, empty, _ => empty

arr16 : Ty16 -> Ty16 -> Ty16
arr16 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con16 : Type
Con16 = (Con16 : Type)
 ->(nil  : Con16)
 ->(snoc : Con16 -> Ty16 -> Con16)
 -> Con16

nil16 : Con16
nil16 = \ con, nil16, snoc => nil16

snoc16 : Con16 -> Ty16 -> Con16
snoc16 = \ g, a, con, nil16, snoc16 => snoc16 (g con nil16 snoc16) a

Var16 : Con16 -> Ty16 -> Type
Var16 = \ g, a =>
    (Var16 : Con16 -> Ty16 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var16 (snoc16 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var16 g a -> Var16 (snoc16 g b) a)
 -> Var16 g a

vz16 : {g : _}-> {a : _} -> Var16 (snoc16 g a) a
vz16 = \ var, vz16, vs => vz16 _ _

vs16 : {g : _} -> {B : _} -> {a : _} -> Var16 g a -> Var16 (snoc16 g B) a
vs16 = \ x, var, vz16, vs16 => vs16 _ _ _ (x var vz16 vs16)

Tm16 : Con16 -> Ty16 -> Type
Tm16 = \ g, a =>
    (Tm16    : Con16 -> Ty16 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var16 g a -> Tm16 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm16 (snoc16 g a) B -> Tm16 g (arr16 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm16 g (arr16 a B) -> Tm16 g a -> Tm16 g B)
 -> Tm16 g a

var16 : {g : _} -> {a : _} -> Var16 g a -> Tm16 g a
var16 = \ x, tm, var16, lam, app => var16 _ _ x

lam16 : {g : _} -> {a : _} -> {B : _} -> Tm16 (snoc16 g a) B -> Tm16 g (arr16 a B)
lam16 = \ t, tm, var16, lam16, app => lam16 _ _ _ (t tm var16 lam16 app)

app16 : {g:_}->{a:_}->{B:_} -> Tm16 g (arr16 a B) -> Tm16 g a -> Tm16 g B
app16 = \ t, u, tm, var16, lam16, app16 => app16 _ _ _ (t tm var16 lam16 app16) (u tm var16 lam16 app16)

v016 : {g:_}->{a:_} -> Tm16 (snoc16 g a) a
v016 = var16 vz16

v116 : {g:_}->{a:_}-> {B:_}-> Tm16 (snoc16 (snoc16 g a) B) a
v116 = var16 (vs16 vz16)

v216 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm16 (snoc16 (snoc16 (snoc16 g a) B) C) a
v216 = var16 (vs16 (vs16 vz16))

v316 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm16 (snoc16 (snoc16 (snoc16 (snoc16 g a) B) C) D) a
v316 = var16 (vs16 (vs16 (vs16 vz16)))

v416 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm16 (snoc16 (snoc16 (snoc16 (snoc16 (snoc16 g a) B) C) D) E) a
v416 = var16 (vs16 (vs16 (vs16 (vs16 vz16))))

test16 : {g:_}-> {a:_} -> Tm16 g (arr16 (arr16 a a) (arr16 a a))
test16  = lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016)))))))
Ty17 : Type
Ty17 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty17 : Ty17
empty17 = \ _, empty, _ => empty

arr17 : Ty17 -> Ty17 -> Ty17
arr17 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con17 : Type
Con17 = (Con17 : Type)
 ->(nil  : Con17)
 ->(snoc : Con17 -> Ty17 -> Con17)
 -> Con17

nil17 : Con17
nil17 = \ con, nil17, snoc => nil17

snoc17 : Con17 -> Ty17 -> Con17
snoc17 = \ g, a, con, nil17, snoc17 => snoc17 (g con nil17 snoc17) a

Var17 : Con17 -> Ty17 -> Type
Var17 = \ g, a =>
    (Var17 : Con17 -> Ty17 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var17 (snoc17 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var17 g a -> Var17 (snoc17 g b) a)
 -> Var17 g a

vz17 : {g : _}-> {a : _} -> Var17 (snoc17 g a) a
vz17 = \ var, vz17, vs => vz17 _ _

vs17 : {g : _} -> {B : _} -> {a : _} -> Var17 g a -> Var17 (snoc17 g B) a
vs17 = \ x, var, vz17, vs17 => vs17 _ _ _ (x var vz17 vs17)

Tm17 : Con17 -> Ty17 -> Type
Tm17 = \ g, a =>
    (Tm17    : Con17 -> Ty17 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var17 g a -> Tm17 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm17 (snoc17 g a) B -> Tm17 g (arr17 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm17 g (arr17 a B) -> Tm17 g a -> Tm17 g B)
 -> Tm17 g a

var17 : {g : _} -> {a : _} -> Var17 g a -> Tm17 g a
var17 = \ x, tm, var17, lam, app => var17 _ _ x

lam17 : {g : _} -> {a : _} -> {B : _} -> Tm17 (snoc17 g a) B -> Tm17 g (arr17 a B)
lam17 = \ t, tm, var17, lam17, app => lam17 _ _ _ (t tm var17 lam17 app)

app17 : {g:_}->{a:_}->{B:_} -> Tm17 g (arr17 a B) -> Tm17 g a -> Tm17 g B
app17 = \ t, u, tm, var17, lam17, app17 => app17 _ _ _ (t tm var17 lam17 app17) (u tm var17 lam17 app17)

v017 : {g:_}->{a:_} -> Tm17 (snoc17 g a) a
v017 = var17 vz17

v117 : {g:_}->{a:_}-> {B:_}-> Tm17 (snoc17 (snoc17 g a) B) a
v117 = var17 (vs17 vz17)

v217 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm17 (snoc17 (snoc17 (snoc17 g a) B) C) a
v217 = var17 (vs17 (vs17 vz17))

v317 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm17 (snoc17 (snoc17 (snoc17 (snoc17 g a) B) C) D) a
v317 = var17 (vs17 (vs17 (vs17 vz17)))

v417 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm17 (snoc17 (snoc17 (snoc17 (snoc17 (snoc17 g a) B) C) D) E) a
v417 = var17 (vs17 (vs17 (vs17 (vs17 vz17))))

test17 : {g:_}-> {a:_} -> Tm17 g (arr17 (arr17 a a) (arr17 a a))
test17  = lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017)))))))
Ty18 : Type
Ty18 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty18 : Ty18
empty18 = \ _, empty, _ => empty

arr18 : Ty18 -> Ty18 -> Ty18
arr18 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con18 : Type
Con18 = (Con18 : Type)
 ->(nil  : Con18)
 ->(snoc : Con18 -> Ty18 -> Con18)
 -> Con18

nil18 : Con18
nil18 = \ con, nil18, snoc => nil18

snoc18 : Con18 -> Ty18 -> Con18
snoc18 = \ g, a, con, nil18, snoc18 => snoc18 (g con nil18 snoc18) a

Var18 : Con18 -> Ty18 -> Type
Var18 = \ g, a =>
    (Var18 : Con18 -> Ty18 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var18 (snoc18 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var18 g a -> Var18 (snoc18 g b) a)
 -> Var18 g a

vz18 : {g : _}-> {a : _} -> Var18 (snoc18 g a) a
vz18 = \ var, vz18, vs => vz18 _ _

vs18 : {g : _} -> {B : _} -> {a : _} -> Var18 g a -> Var18 (snoc18 g B) a
vs18 = \ x, var, vz18, vs18 => vs18 _ _ _ (x var vz18 vs18)

Tm18 : Con18 -> Ty18 -> Type
Tm18 = \ g, a =>
    (Tm18    : Con18 -> Ty18 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var18 g a -> Tm18 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm18 (snoc18 g a) B -> Tm18 g (arr18 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm18 g (arr18 a B) -> Tm18 g a -> Tm18 g B)
 -> Tm18 g a

var18 : {g : _} -> {a : _} -> Var18 g a -> Tm18 g a
var18 = \ x, tm, var18, lam, app => var18 _ _ x

lam18 : {g : _} -> {a : _} -> {B : _} -> Tm18 (snoc18 g a) B -> Tm18 g (arr18 a B)
lam18 = \ t, tm, var18, lam18, app => lam18 _ _ _ (t tm var18 lam18 app)

app18 : {g:_}->{a:_}->{B:_} -> Tm18 g (arr18 a B) -> Tm18 g a -> Tm18 g B
app18 = \ t, u, tm, var18, lam18, app18 => app18 _ _ _ (t tm var18 lam18 app18) (u tm var18 lam18 app18)

v018 : {g:_}->{a:_} -> Tm18 (snoc18 g a) a
v018 = var18 vz18

v118 : {g:_}->{a:_}-> {B:_}-> Tm18 (snoc18 (snoc18 g a) B) a
v118 = var18 (vs18 vz18)

v218 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm18 (snoc18 (snoc18 (snoc18 g a) B) C) a
v218 = var18 (vs18 (vs18 vz18))

v318 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm18 (snoc18 (snoc18 (snoc18 (snoc18 g a) B) C) D) a
v318 = var18 (vs18 (vs18 (vs18 vz18)))

v418 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm18 (snoc18 (snoc18 (snoc18 (snoc18 (snoc18 g a) B) C) D) E) a
v418 = var18 (vs18 (vs18 (vs18 (vs18 vz18))))

test18 : {g:_}-> {a:_} -> Tm18 g (arr18 (arr18 a a) (arr18 a a))
test18  = lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018)))))))
Ty19 : Type
Ty19 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty19 : Ty19
empty19 = \ _, empty, _ => empty

arr19 : Ty19 -> Ty19 -> Ty19
arr19 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con19 : Type
Con19 = (Con19 : Type)
 ->(nil  : Con19)
 ->(snoc : Con19 -> Ty19 -> Con19)
 -> Con19

nil19 : Con19
nil19 = \ con, nil19, snoc => nil19

snoc19 : Con19 -> Ty19 -> Con19
snoc19 = \ g, a, con, nil19, snoc19 => snoc19 (g con nil19 snoc19) a

Var19 : Con19 -> Ty19 -> Type
Var19 = \ g, a =>
    (Var19 : Con19 -> Ty19 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var19 (snoc19 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var19 g a -> Var19 (snoc19 g b) a)
 -> Var19 g a

vz19 : {g : _}-> {a : _} -> Var19 (snoc19 g a) a
vz19 = \ var, vz19, vs => vz19 _ _

vs19 : {g : _} -> {B : _} -> {a : _} -> Var19 g a -> Var19 (snoc19 g B) a
vs19 = \ x, var, vz19, vs19 => vs19 _ _ _ (x var vz19 vs19)

Tm19 : Con19 -> Ty19 -> Type
Tm19 = \ g, a =>
    (Tm19    : Con19 -> Ty19 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var19 g a -> Tm19 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm19 (snoc19 g a) B -> Tm19 g (arr19 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm19 g (arr19 a B) -> Tm19 g a -> Tm19 g B)
 -> Tm19 g a

var19 : {g : _} -> {a : _} -> Var19 g a -> Tm19 g a
var19 = \ x, tm, var19, lam, app => var19 _ _ x

lam19 : {g : _} -> {a : _} -> {B : _} -> Tm19 (snoc19 g a) B -> Tm19 g (arr19 a B)
lam19 = \ t, tm, var19, lam19, app => lam19 _ _ _ (t tm var19 lam19 app)

app19 : {g:_}->{a:_}->{B:_} -> Tm19 g (arr19 a B) -> Tm19 g a -> Tm19 g B
app19 = \ t, u, tm, var19, lam19, app19 => app19 _ _ _ (t tm var19 lam19 app19) (u tm var19 lam19 app19)

v019 : {g:_}->{a:_} -> Tm19 (snoc19 g a) a
v019 = var19 vz19

v119 : {g:_}->{a:_}-> {B:_}-> Tm19 (snoc19 (snoc19 g a) B) a
v119 = var19 (vs19 vz19)

v219 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm19 (snoc19 (snoc19 (snoc19 g a) B) C) a
v219 = var19 (vs19 (vs19 vz19))

v319 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm19 (snoc19 (snoc19 (snoc19 (snoc19 g a) B) C) D) a
v319 = var19 (vs19 (vs19 (vs19 vz19)))

v419 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm19 (snoc19 (snoc19 (snoc19 (snoc19 (snoc19 g a) B) C) D) E) a
v419 = var19 (vs19 (vs19 (vs19 (vs19 vz19))))

test19 : {g:_}-> {a:_} -> Tm19 g (arr19 (arr19 a a) (arr19 a a))
test19  = lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019)))))))
Ty20 : Type
Ty20 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty20 : Ty20
empty20 = \ _, empty, _ => empty

arr20 : Ty20 -> Ty20 -> Ty20
arr20 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con20 : Type
Con20 = (Con20 : Type)
 ->(nil  : Con20)
 ->(snoc : Con20 -> Ty20 -> Con20)
 -> Con20

nil20 : Con20
nil20 = \ con, nil20, snoc => nil20

snoc20 : Con20 -> Ty20 -> Con20
snoc20 = \ g, a, con, nil20, snoc20 => snoc20 (g con nil20 snoc20) a

Var20 : Con20 -> Ty20 -> Type
Var20 = \ g, a =>
    (Var20 : Con20 -> Ty20 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var20 (snoc20 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var20 g a -> Var20 (snoc20 g b) a)
 -> Var20 g a

vz20 : {g : _}-> {a : _} -> Var20 (snoc20 g a) a
vz20 = \ var, vz20, vs => vz20 _ _

vs20 : {g : _} -> {B : _} -> {a : _} -> Var20 g a -> Var20 (snoc20 g B) a
vs20 = \ x, var, vz20, vs20 => vs20 _ _ _ (x var vz20 vs20)

Tm20 : Con20 -> Ty20 -> Type
Tm20 = \ g, a =>
    (Tm20    : Con20 -> Ty20 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var20 g a -> Tm20 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm20 (snoc20 g a) B -> Tm20 g (arr20 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm20 g (arr20 a B) -> Tm20 g a -> Tm20 g B)
 -> Tm20 g a

var20 : {g : _} -> {a : _} -> Var20 g a -> Tm20 g a
var20 = \ x, tm, var20, lam, app => var20 _ _ x

lam20 : {g : _} -> {a : _} -> {B : _} -> Tm20 (snoc20 g a) B -> Tm20 g (arr20 a B)
lam20 = \ t, tm, var20, lam20, app => lam20 _ _ _ (t tm var20 lam20 app)

app20 : {g:_}->{a:_}->{B:_} -> Tm20 g (arr20 a B) -> Tm20 g a -> Tm20 g B
app20 = \ t, u, tm, var20, lam20, app20 => app20 _ _ _ (t tm var20 lam20 app20) (u tm var20 lam20 app20)

v020 : {g:_}->{a:_} -> Tm20 (snoc20 g a) a
v020 = var20 vz20

v120 : {g:_}->{a:_}-> {B:_}-> Tm20 (snoc20 (snoc20 g a) B) a
v120 = var20 (vs20 vz20)

v220 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm20 (snoc20 (snoc20 (snoc20 g a) B) C) a
v220 = var20 (vs20 (vs20 vz20))

v320 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm20 (snoc20 (snoc20 (snoc20 (snoc20 g a) B) C) D) a
v320 = var20 (vs20 (vs20 (vs20 vz20)))

v420 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm20 (snoc20 (snoc20 (snoc20 (snoc20 (snoc20 g a) B) C) D) E) a
v420 = var20 (vs20 (vs20 (vs20 (vs20 vz20))))

test20 : {g:_}-> {a:_} -> Tm20 g (arr20 (arr20 a a) (arr20 a a))
test20  = lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020)))))))
Ty21 : Type
Ty21 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty21 : Ty21
empty21 = \ _, empty, _ => empty

arr21 : Ty21 -> Ty21 -> Ty21
arr21 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con21 : Type
Con21 = (Con21 : Type)
 ->(nil  : Con21)
 ->(snoc : Con21 -> Ty21 -> Con21)
 -> Con21

nil21 : Con21
nil21 = \ con, nil21, snoc => nil21

snoc21 : Con21 -> Ty21 -> Con21
snoc21 = \ g, a, con, nil21, snoc21 => snoc21 (g con nil21 snoc21) a

Var21 : Con21 -> Ty21 -> Type
Var21 = \ g, a =>
    (Var21 : Con21 -> Ty21 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var21 (snoc21 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var21 g a -> Var21 (snoc21 g b) a)
 -> Var21 g a

vz21 : {g : _}-> {a : _} -> Var21 (snoc21 g a) a
vz21 = \ var, vz21, vs => vz21 _ _

vs21 : {g : _} -> {B : _} -> {a : _} -> Var21 g a -> Var21 (snoc21 g B) a
vs21 = \ x, var, vz21, vs21 => vs21 _ _ _ (x var vz21 vs21)

Tm21 : Con21 -> Ty21 -> Type
Tm21 = \ g, a =>
    (Tm21    : Con21 -> Ty21 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var21 g a -> Tm21 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm21 (snoc21 g a) B -> Tm21 g (arr21 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm21 g (arr21 a B) -> Tm21 g a -> Tm21 g B)
 -> Tm21 g a

var21 : {g : _} -> {a : _} -> Var21 g a -> Tm21 g a
var21 = \ x, tm, var21, lam, app => var21 _ _ x

lam21 : {g : _} -> {a : _} -> {B : _} -> Tm21 (snoc21 g a) B -> Tm21 g (arr21 a B)
lam21 = \ t, tm, var21, lam21, app => lam21 _ _ _ (t tm var21 lam21 app)

app21 : {g:_}->{a:_}->{B:_} -> Tm21 g (arr21 a B) -> Tm21 g a -> Tm21 g B
app21 = \ t, u, tm, var21, lam21, app21 => app21 _ _ _ (t tm var21 lam21 app21) (u tm var21 lam21 app21)

v021 : {g:_}->{a:_} -> Tm21 (snoc21 g a) a
v021 = var21 vz21

v121 : {g:_}->{a:_}-> {B:_}-> Tm21 (snoc21 (snoc21 g a) B) a
v121 = var21 (vs21 vz21)

v221 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm21 (snoc21 (snoc21 (snoc21 g a) B) C) a
v221 = var21 (vs21 (vs21 vz21))

v321 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm21 (snoc21 (snoc21 (snoc21 (snoc21 g a) B) C) D) a
v321 = var21 (vs21 (vs21 (vs21 vz21)))

v421 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm21 (snoc21 (snoc21 (snoc21 (snoc21 (snoc21 g a) B) C) D) E) a
v421 = var21 (vs21 (vs21 (vs21 (vs21 vz21))))

test21 : {g:_}-> {a:_} -> Tm21 g (arr21 (arr21 a a) (arr21 a a))
test21  = lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021)))))))
Ty22 : Type
Ty22 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty22 : Ty22
empty22 = \ _, empty, _ => empty

arr22 : Ty22 -> Ty22 -> Ty22
arr22 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con22 : Type
Con22 = (Con22 : Type)
 ->(nil  : Con22)
 ->(snoc : Con22 -> Ty22 -> Con22)
 -> Con22

nil22 : Con22
nil22 = \ con, nil22, snoc => nil22

snoc22 : Con22 -> Ty22 -> Con22
snoc22 = \ g, a, con, nil22, snoc22 => snoc22 (g con nil22 snoc22) a

Var22 : Con22 -> Ty22 -> Type
Var22 = \ g, a =>
    (Var22 : Con22 -> Ty22 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var22 (snoc22 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var22 g a -> Var22 (snoc22 g b) a)
 -> Var22 g a

vz22 : {g : _}-> {a : _} -> Var22 (snoc22 g a) a
vz22 = \ var, vz22, vs => vz22 _ _

vs22 : {g : _} -> {B : _} -> {a : _} -> Var22 g a -> Var22 (snoc22 g B) a
vs22 = \ x, var, vz22, vs22 => vs22 _ _ _ (x var vz22 vs22)

Tm22 : Con22 -> Ty22 -> Type
Tm22 = \ g, a =>
    (Tm22    : Con22 -> Ty22 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var22 g a -> Tm22 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm22 (snoc22 g a) B -> Tm22 g (arr22 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm22 g (arr22 a B) -> Tm22 g a -> Tm22 g B)
 -> Tm22 g a

var22 : {g : _} -> {a : _} -> Var22 g a -> Tm22 g a
var22 = \ x, tm, var22, lam, app => var22 _ _ x

lam22 : {g : _} -> {a : _} -> {B : _} -> Tm22 (snoc22 g a) B -> Tm22 g (arr22 a B)
lam22 = \ t, tm, var22, lam22, app => lam22 _ _ _ (t tm var22 lam22 app)

app22 : {g:_}->{a:_}->{B:_} -> Tm22 g (arr22 a B) -> Tm22 g a -> Tm22 g B
app22 = \ t, u, tm, var22, lam22, app22 => app22 _ _ _ (t tm var22 lam22 app22) (u tm var22 lam22 app22)

v022 : {g:_}->{a:_} -> Tm22 (snoc22 g a) a
v022 = var22 vz22

v122 : {g:_}->{a:_}-> {B:_}-> Tm22 (snoc22 (snoc22 g a) B) a
v122 = var22 (vs22 vz22)

v222 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm22 (snoc22 (snoc22 (snoc22 g a) B) C) a
v222 = var22 (vs22 (vs22 vz22))

v322 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm22 (snoc22 (snoc22 (snoc22 (snoc22 g a) B) C) D) a
v322 = var22 (vs22 (vs22 (vs22 vz22)))

v422 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm22 (snoc22 (snoc22 (snoc22 (snoc22 (snoc22 g a) B) C) D) E) a
v422 = var22 (vs22 (vs22 (vs22 (vs22 vz22))))

test22 : {g:_}-> {a:_} -> Tm22 g (arr22 (arr22 a a) (arr22 a a))
test22  = lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022)))))))
Ty23 : Type
Ty23 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty23 : Ty23
empty23 = \ _, empty, _ => empty

arr23 : Ty23 -> Ty23 -> Ty23
arr23 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con23 : Type
Con23 = (Con23 : Type)
 ->(nil  : Con23)
 ->(snoc : Con23 -> Ty23 -> Con23)
 -> Con23

nil23 : Con23
nil23 = \ con, nil23, snoc => nil23

snoc23 : Con23 -> Ty23 -> Con23
snoc23 = \ g, a, con, nil23, snoc23 => snoc23 (g con nil23 snoc23) a

Var23 : Con23 -> Ty23 -> Type
Var23 = \ g, a =>
    (Var23 : Con23 -> Ty23 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var23 (snoc23 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var23 g a -> Var23 (snoc23 g b) a)
 -> Var23 g a

vz23 : {g : _}-> {a : _} -> Var23 (snoc23 g a) a
vz23 = \ var, vz23, vs => vz23 _ _

vs23 : {g : _} -> {B : _} -> {a : _} -> Var23 g a -> Var23 (snoc23 g B) a
vs23 = \ x, var, vz23, vs23 => vs23 _ _ _ (x var vz23 vs23)

Tm23 : Con23 -> Ty23 -> Type
Tm23 = \ g, a =>
    (Tm23    : Con23 -> Ty23 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var23 g a -> Tm23 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm23 (snoc23 g a) B -> Tm23 g (arr23 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm23 g (arr23 a B) -> Tm23 g a -> Tm23 g B)
 -> Tm23 g a

var23 : {g : _} -> {a : _} -> Var23 g a -> Tm23 g a
var23 = \ x, tm, var23, lam, app => var23 _ _ x

lam23 : {g : _} -> {a : _} -> {B : _} -> Tm23 (snoc23 g a) B -> Tm23 g (arr23 a B)
lam23 = \ t, tm, var23, lam23, app => lam23 _ _ _ (t tm var23 lam23 app)

app23 : {g:_}->{a:_}->{B:_} -> Tm23 g (arr23 a B) -> Tm23 g a -> Tm23 g B
app23 = \ t, u, tm, var23, lam23, app23 => app23 _ _ _ (t tm var23 lam23 app23) (u tm var23 lam23 app23)

v023 : {g:_}->{a:_} -> Tm23 (snoc23 g a) a
v023 = var23 vz23

v123 : {g:_}->{a:_}-> {B:_}-> Tm23 (snoc23 (snoc23 g a) B) a
v123 = var23 (vs23 vz23)

v223 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm23 (snoc23 (snoc23 (snoc23 g a) B) C) a
v223 = var23 (vs23 (vs23 vz23))

v323 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm23 (snoc23 (snoc23 (snoc23 (snoc23 g a) B) C) D) a
v323 = var23 (vs23 (vs23 (vs23 vz23)))

v423 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm23 (snoc23 (snoc23 (snoc23 (snoc23 (snoc23 g a) B) C) D) E) a
v423 = var23 (vs23 (vs23 (vs23 (vs23 vz23))))

test23 : {g:_}-> {a:_} -> Tm23 g (arr23 (arr23 a a) (arr23 a a))
test23  = lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023)))))))
Ty24 : Type
Ty24 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty24 : Ty24
empty24 = \ _, empty, _ => empty

arr24 : Ty24 -> Ty24 -> Ty24
arr24 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con24 : Type
Con24 = (Con24 : Type)
 ->(nil  : Con24)
 ->(snoc : Con24 -> Ty24 -> Con24)
 -> Con24

nil24 : Con24
nil24 = \ con, nil24, snoc => nil24

snoc24 : Con24 -> Ty24 -> Con24
snoc24 = \ g, a, con, nil24, snoc24 => snoc24 (g con nil24 snoc24) a

Var24 : Con24 -> Ty24 -> Type
Var24 = \ g, a =>
    (Var24 : Con24 -> Ty24 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var24 (snoc24 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var24 g a -> Var24 (snoc24 g b) a)
 -> Var24 g a

vz24 : {g : _}-> {a : _} -> Var24 (snoc24 g a) a
vz24 = \ var, vz24, vs => vz24 _ _

vs24 : {g : _} -> {B : _} -> {a : _} -> Var24 g a -> Var24 (snoc24 g B) a
vs24 = \ x, var, vz24, vs24 => vs24 _ _ _ (x var vz24 vs24)

Tm24 : Con24 -> Ty24 -> Type
Tm24 = \ g, a =>
    (Tm24    : Con24 -> Ty24 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var24 g a -> Tm24 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm24 (snoc24 g a) B -> Tm24 g (arr24 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm24 g (arr24 a B) -> Tm24 g a -> Tm24 g B)
 -> Tm24 g a

var24 : {g : _} -> {a : _} -> Var24 g a -> Tm24 g a
var24 = \ x, tm, var24, lam, app => var24 _ _ x

lam24 : {g : _} -> {a : _} -> {B : _} -> Tm24 (snoc24 g a) B -> Tm24 g (arr24 a B)
lam24 = \ t, tm, var24, lam24, app => lam24 _ _ _ (t tm var24 lam24 app)

app24 : {g:_}->{a:_}->{B:_} -> Tm24 g (arr24 a B) -> Tm24 g a -> Tm24 g B
app24 = \ t, u, tm, var24, lam24, app24 => app24 _ _ _ (t tm var24 lam24 app24) (u tm var24 lam24 app24)

v024 : {g:_}->{a:_} -> Tm24 (snoc24 g a) a
v024 = var24 vz24

v124 : {g:_}->{a:_}-> {B:_}-> Tm24 (snoc24 (snoc24 g a) B) a
v124 = var24 (vs24 vz24)

v224 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm24 (snoc24 (snoc24 (snoc24 g a) B) C) a
v224 = var24 (vs24 (vs24 vz24))

v324 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm24 (snoc24 (snoc24 (snoc24 (snoc24 g a) B) C) D) a
v324 = var24 (vs24 (vs24 (vs24 vz24)))

v424 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm24 (snoc24 (snoc24 (snoc24 (snoc24 (snoc24 g a) B) C) D) E) a
v424 = var24 (vs24 (vs24 (vs24 (vs24 vz24))))

test24 : {g:_}-> {a:_} -> Tm24 g (arr24 (arr24 a a) (arr24 a a))
test24  = lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024)))))))
Ty25 : Type
Ty25 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty25 : Ty25
empty25 = \ _, empty, _ => empty

arr25 : Ty25 -> Ty25 -> Ty25
arr25 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con25 : Type
Con25 = (Con25 : Type)
 ->(nil  : Con25)
 ->(snoc : Con25 -> Ty25 -> Con25)
 -> Con25

nil25 : Con25
nil25 = \ con, nil25, snoc => nil25

snoc25 : Con25 -> Ty25 -> Con25
snoc25 = \ g, a, con, nil25, snoc25 => snoc25 (g con nil25 snoc25) a

Var25 : Con25 -> Ty25 -> Type
Var25 = \ g, a =>
    (Var25 : Con25 -> Ty25 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var25 (snoc25 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var25 g a -> Var25 (snoc25 g b) a)
 -> Var25 g a

vz25 : {g : _}-> {a : _} -> Var25 (snoc25 g a) a
vz25 = \ var, vz25, vs => vz25 _ _

vs25 : {g : _} -> {B : _} -> {a : _} -> Var25 g a -> Var25 (snoc25 g B) a
vs25 = \ x, var, vz25, vs25 => vs25 _ _ _ (x var vz25 vs25)

Tm25 : Con25 -> Ty25 -> Type
Tm25 = \ g, a =>
    (Tm25    : Con25 -> Ty25 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var25 g a -> Tm25 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm25 (snoc25 g a) B -> Tm25 g (arr25 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm25 g (arr25 a B) -> Tm25 g a -> Tm25 g B)
 -> Tm25 g a

var25 : {g : _} -> {a : _} -> Var25 g a -> Tm25 g a
var25 = \ x, tm, var25, lam, app => var25 _ _ x

lam25 : {g : _} -> {a : _} -> {B : _} -> Tm25 (snoc25 g a) B -> Tm25 g (arr25 a B)
lam25 = \ t, tm, var25, lam25, app => lam25 _ _ _ (t tm var25 lam25 app)

app25 : {g:_}->{a:_}->{B:_} -> Tm25 g (arr25 a B) -> Tm25 g a -> Tm25 g B
app25 = \ t, u, tm, var25, lam25, app25 => app25 _ _ _ (t tm var25 lam25 app25) (u tm var25 lam25 app25)

v025 : {g:_}->{a:_} -> Tm25 (snoc25 g a) a
v025 = var25 vz25

v125 : {g:_}->{a:_}-> {B:_}-> Tm25 (snoc25 (snoc25 g a) B) a
v125 = var25 (vs25 vz25)

v225 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm25 (snoc25 (snoc25 (snoc25 g a) B) C) a
v225 = var25 (vs25 (vs25 vz25))

v325 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm25 (snoc25 (snoc25 (snoc25 (snoc25 g a) B) C) D) a
v325 = var25 (vs25 (vs25 (vs25 vz25)))

v425 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm25 (snoc25 (snoc25 (snoc25 (snoc25 (snoc25 g a) B) C) D) E) a
v425 = var25 (vs25 (vs25 (vs25 (vs25 vz25))))

test25 : {g:_}-> {a:_} -> Tm25 g (arr25 (arr25 a a) (arr25 a a))
test25  = lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025)))))))
Ty26 : Type
Ty26 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty26 : Ty26
empty26 = \ _, empty, _ => empty

arr26 : Ty26 -> Ty26 -> Ty26
arr26 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con26 : Type
Con26 = (Con26 : Type)
 ->(nil  : Con26)
 ->(snoc : Con26 -> Ty26 -> Con26)
 -> Con26

nil26 : Con26
nil26 = \ con, nil26, snoc => nil26

snoc26 : Con26 -> Ty26 -> Con26
snoc26 = \ g, a, con, nil26, snoc26 => snoc26 (g con nil26 snoc26) a

Var26 : Con26 -> Ty26 -> Type
Var26 = \ g, a =>
    (Var26 : Con26 -> Ty26 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var26 (snoc26 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var26 g a -> Var26 (snoc26 g b) a)
 -> Var26 g a

vz26 : {g : _}-> {a : _} -> Var26 (snoc26 g a) a
vz26 = \ var, vz26, vs => vz26 _ _

vs26 : {g : _} -> {B : _} -> {a : _} -> Var26 g a -> Var26 (snoc26 g B) a
vs26 = \ x, var, vz26, vs26 => vs26 _ _ _ (x var vz26 vs26)

Tm26 : Con26 -> Ty26 -> Type
Tm26 = \ g, a =>
    (Tm26    : Con26 -> Ty26 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var26 g a -> Tm26 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm26 (snoc26 g a) B -> Tm26 g (arr26 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm26 g (arr26 a B) -> Tm26 g a -> Tm26 g B)
 -> Tm26 g a

var26 : {g : _} -> {a : _} -> Var26 g a -> Tm26 g a
var26 = \ x, tm, var26, lam, app => var26 _ _ x

lam26 : {g : _} -> {a : _} -> {B : _} -> Tm26 (snoc26 g a) B -> Tm26 g (arr26 a B)
lam26 = \ t, tm, var26, lam26, app => lam26 _ _ _ (t tm var26 lam26 app)

app26 : {g:_}->{a:_}->{B:_} -> Tm26 g (arr26 a B) -> Tm26 g a -> Tm26 g B
app26 = \ t, u, tm, var26, lam26, app26 => app26 _ _ _ (t tm var26 lam26 app26) (u tm var26 lam26 app26)

v026 : {g:_}->{a:_} -> Tm26 (snoc26 g a) a
v026 = var26 vz26

v126 : {g:_}->{a:_}-> {B:_}-> Tm26 (snoc26 (snoc26 g a) B) a
v126 = var26 (vs26 vz26)

v226 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm26 (snoc26 (snoc26 (snoc26 g a) B) C) a
v226 = var26 (vs26 (vs26 vz26))

v326 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm26 (snoc26 (snoc26 (snoc26 (snoc26 g a) B) C) D) a
v326 = var26 (vs26 (vs26 (vs26 vz26)))

v426 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm26 (snoc26 (snoc26 (snoc26 (snoc26 (snoc26 g a) B) C) D) E) a
v426 = var26 (vs26 (vs26 (vs26 (vs26 vz26))))

test26 : {g:_}-> {a:_} -> Tm26 g (arr26 (arr26 a a) (arr26 a a))
test26  = lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026)))))))
Ty27 : Type
Ty27 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty27 : Ty27
empty27 = \ _, empty, _ => empty

arr27 : Ty27 -> Ty27 -> Ty27
arr27 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con27 : Type
Con27 = (Con27 : Type)
 ->(nil  : Con27)
 ->(snoc : Con27 -> Ty27 -> Con27)
 -> Con27

nil27 : Con27
nil27 = \ con, nil27, snoc => nil27

snoc27 : Con27 -> Ty27 -> Con27
snoc27 = \ g, a, con, nil27, snoc27 => snoc27 (g con nil27 snoc27) a

Var27 : Con27 -> Ty27 -> Type
Var27 = \ g, a =>
    (Var27 : Con27 -> Ty27 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var27 (snoc27 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var27 g a -> Var27 (snoc27 g b) a)
 -> Var27 g a

vz27 : {g : _}-> {a : _} -> Var27 (snoc27 g a) a
vz27 = \ var, vz27, vs => vz27 _ _

vs27 : {g : _} -> {B : _} -> {a : _} -> Var27 g a -> Var27 (snoc27 g B) a
vs27 = \ x, var, vz27, vs27 => vs27 _ _ _ (x var vz27 vs27)

Tm27 : Con27 -> Ty27 -> Type
Tm27 = \ g, a =>
    (Tm27    : Con27 -> Ty27 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var27 g a -> Tm27 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm27 (snoc27 g a) B -> Tm27 g (arr27 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm27 g (arr27 a B) -> Tm27 g a -> Tm27 g B)
 -> Tm27 g a

var27 : {g : _} -> {a : _} -> Var27 g a -> Tm27 g a
var27 = \ x, tm, var27, lam, app => var27 _ _ x

lam27 : {g : _} -> {a : _} -> {B : _} -> Tm27 (snoc27 g a) B -> Tm27 g (arr27 a B)
lam27 = \ t, tm, var27, lam27, app => lam27 _ _ _ (t tm var27 lam27 app)

app27 : {g:_}->{a:_}->{B:_} -> Tm27 g (arr27 a B) -> Tm27 g a -> Tm27 g B
app27 = \ t, u, tm, var27, lam27, app27 => app27 _ _ _ (t tm var27 lam27 app27) (u tm var27 lam27 app27)

v027 : {g:_}->{a:_} -> Tm27 (snoc27 g a) a
v027 = var27 vz27

v127 : {g:_}->{a:_}-> {B:_}-> Tm27 (snoc27 (snoc27 g a) B) a
v127 = var27 (vs27 vz27)

v227 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm27 (snoc27 (snoc27 (snoc27 g a) B) C) a
v227 = var27 (vs27 (vs27 vz27))

v327 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm27 (snoc27 (snoc27 (snoc27 (snoc27 g a) B) C) D) a
v327 = var27 (vs27 (vs27 (vs27 vz27)))

v427 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm27 (snoc27 (snoc27 (snoc27 (snoc27 (snoc27 g a) B) C) D) E) a
v427 = var27 (vs27 (vs27 (vs27 (vs27 vz27))))

test27 : {g:_}-> {a:_} -> Tm27 g (arr27 (arr27 a a) (arr27 a a))
test27  = lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027)))))))
Ty28 : Type
Ty28 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty28 : Ty28
empty28 = \ _, empty, _ => empty

arr28 : Ty28 -> Ty28 -> Ty28
arr28 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con28 : Type
Con28 = (Con28 : Type)
 ->(nil  : Con28)
 ->(snoc : Con28 -> Ty28 -> Con28)
 -> Con28

nil28 : Con28
nil28 = \ con, nil28, snoc => nil28

snoc28 : Con28 -> Ty28 -> Con28
snoc28 = \ g, a, con, nil28, snoc28 => snoc28 (g con nil28 snoc28) a

Var28 : Con28 -> Ty28 -> Type
Var28 = \ g, a =>
    (Var28 : Con28 -> Ty28 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var28 (snoc28 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var28 g a -> Var28 (snoc28 g b) a)
 -> Var28 g a

vz28 : {g : _}-> {a : _} -> Var28 (snoc28 g a) a
vz28 = \ var, vz28, vs => vz28 _ _

vs28 : {g : _} -> {B : _} -> {a : _} -> Var28 g a -> Var28 (snoc28 g B) a
vs28 = \ x, var, vz28, vs28 => vs28 _ _ _ (x var vz28 vs28)

Tm28 : Con28 -> Ty28 -> Type
Tm28 = \ g, a =>
    (Tm28    : Con28 -> Ty28 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var28 g a -> Tm28 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm28 (snoc28 g a) B -> Tm28 g (arr28 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm28 g (arr28 a B) -> Tm28 g a -> Tm28 g B)
 -> Tm28 g a

var28 : {g : _} -> {a : _} -> Var28 g a -> Tm28 g a
var28 = \ x, tm, var28, lam, app => var28 _ _ x

lam28 : {g : _} -> {a : _} -> {B : _} -> Tm28 (snoc28 g a) B -> Tm28 g (arr28 a B)
lam28 = \ t, tm, var28, lam28, app => lam28 _ _ _ (t tm var28 lam28 app)

app28 : {g:_}->{a:_}->{B:_} -> Tm28 g (arr28 a B) -> Tm28 g a -> Tm28 g B
app28 = \ t, u, tm, var28, lam28, app28 => app28 _ _ _ (t tm var28 lam28 app28) (u tm var28 lam28 app28)

v028 : {g:_}->{a:_} -> Tm28 (snoc28 g a) a
v028 = var28 vz28

v128 : {g:_}->{a:_}-> {B:_}-> Tm28 (snoc28 (snoc28 g a) B) a
v128 = var28 (vs28 vz28)

v228 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm28 (snoc28 (snoc28 (snoc28 g a) B) C) a
v228 = var28 (vs28 (vs28 vz28))

v328 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm28 (snoc28 (snoc28 (snoc28 (snoc28 g a) B) C) D) a
v328 = var28 (vs28 (vs28 (vs28 vz28)))

v428 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm28 (snoc28 (snoc28 (snoc28 (snoc28 (snoc28 g a) B) C) D) E) a
v428 = var28 (vs28 (vs28 (vs28 (vs28 vz28))))

test28 : {g:_}-> {a:_} -> Tm28 g (arr28 (arr28 a a) (arr28 a a))
test28  = lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028)))))))
Ty29 : Type
Ty29 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty29 : Ty29
empty29 = \ _, empty, _ => empty

arr29 : Ty29 -> Ty29 -> Ty29
arr29 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con29 : Type
Con29 = (Con29 : Type)
 ->(nil  : Con29)
 ->(snoc : Con29 -> Ty29 -> Con29)
 -> Con29

nil29 : Con29
nil29 = \ con, nil29, snoc => nil29

snoc29 : Con29 -> Ty29 -> Con29
snoc29 = \ g, a, con, nil29, snoc29 => snoc29 (g con nil29 snoc29) a

Var29 : Con29 -> Ty29 -> Type
Var29 = \ g, a =>
    (Var29 : Con29 -> Ty29 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var29 (snoc29 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var29 g a -> Var29 (snoc29 g b) a)
 -> Var29 g a

vz29 : {g : _}-> {a : _} -> Var29 (snoc29 g a) a
vz29 = \ var, vz29, vs => vz29 _ _

vs29 : {g : _} -> {B : _} -> {a : _} -> Var29 g a -> Var29 (snoc29 g B) a
vs29 = \ x, var, vz29, vs29 => vs29 _ _ _ (x var vz29 vs29)

Tm29 : Con29 -> Ty29 -> Type
Tm29 = \ g, a =>
    (Tm29    : Con29 -> Ty29 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var29 g a -> Tm29 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm29 (snoc29 g a) B -> Tm29 g (arr29 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm29 g (arr29 a B) -> Tm29 g a -> Tm29 g B)
 -> Tm29 g a

var29 : {g : _} -> {a : _} -> Var29 g a -> Tm29 g a
var29 = \ x, tm, var29, lam, app => var29 _ _ x

lam29 : {g : _} -> {a : _} -> {B : _} -> Tm29 (snoc29 g a) B -> Tm29 g (arr29 a B)
lam29 = \ t, tm, var29, lam29, app => lam29 _ _ _ (t tm var29 lam29 app)

app29 : {g:_}->{a:_}->{B:_} -> Tm29 g (arr29 a B) -> Tm29 g a -> Tm29 g B
app29 = \ t, u, tm, var29, lam29, app29 => app29 _ _ _ (t tm var29 lam29 app29) (u tm var29 lam29 app29)

v029 : {g:_}->{a:_} -> Tm29 (snoc29 g a) a
v029 = var29 vz29

v129 : {g:_}->{a:_}-> {B:_}-> Tm29 (snoc29 (snoc29 g a) B) a
v129 = var29 (vs29 vz29)

v229 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm29 (snoc29 (snoc29 (snoc29 g a) B) C) a
v229 = var29 (vs29 (vs29 vz29))

v329 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm29 (snoc29 (snoc29 (snoc29 (snoc29 g a) B) C) D) a
v329 = var29 (vs29 (vs29 (vs29 vz29)))

v429 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm29 (snoc29 (snoc29 (snoc29 (snoc29 (snoc29 g a) B) C) D) E) a
v429 = var29 (vs29 (vs29 (vs29 (vs29 vz29))))

test29 : {g:_}-> {a:_} -> Tm29 g (arr29 (arr29 a a) (arr29 a a))
test29  = lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029)))))))
Ty30 : Type
Ty30 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty30 : Ty30
empty30 = \ _, empty, _ => empty

arr30 : Ty30 -> Ty30 -> Ty30
arr30 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con30 : Type
Con30 = (Con30 : Type)
 ->(nil  : Con30)
 ->(snoc : Con30 -> Ty30 -> Con30)
 -> Con30

nil30 : Con30
nil30 = \ con, nil30, snoc => nil30

snoc30 : Con30 -> Ty30 -> Con30
snoc30 = \ g, a, con, nil30, snoc30 => snoc30 (g con nil30 snoc30) a

Var30 : Con30 -> Ty30 -> Type
Var30 = \ g, a =>
    (Var30 : Con30 -> Ty30 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var30 (snoc30 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var30 g a -> Var30 (snoc30 g b) a)
 -> Var30 g a

vz30 : {g : _}-> {a : _} -> Var30 (snoc30 g a) a
vz30 = \ var, vz30, vs => vz30 _ _

vs30 : {g : _} -> {B : _} -> {a : _} -> Var30 g a -> Var30 (snoc30 g B) a
vs30 = \ x, var, vz30, vs30 => vs30 _ _ _ (x var vz30 vs30)

Tm30 : Con30 -> Ty30 -> Type
Tm30 = \ g, a =>
    (Tm30    : Con30 -> Ty30 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var30 g a -> Tm30 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm30 (snoc30 g a) B -> Tm30 g (arr30 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm30 g (arr30 a B) -> Tm30 g a -> Tm30 g B)
 -> Tm30 g a

var30 : {g : _} -> {a : _} -> Var30 g a -> Tm30 g a
var30 = \ x, tm, var30, lam, app => var30 _ _ x

lam30 : {g : _} -> {a : _} -> {B : _} -> Tm30 (snoc30 g a) B -> Tm30 g (arr30 a B)
lam30 = \ t, tm, var30, lam30, app => lam30 _ _ _ (t tm var30 lam30 app)

app30 : {g:_}->{a:_}->{B:_} -> Tm30 g (arr30 a B) -> Tm30 g a -> Tm30 g B
app30 = \ t, u, tm, var30, lam30, app30 => app30 _ _ _ (t tm var30 lam30 app30) (u tm var30 lam30 app30)

v030 : {g:_}->{a:_} -> Tm30 (snoc30 g a) a
v030 = var30 vz30

v130 : {g:_}->{a:_}-> {B:_}-> Tm30 (snoc30 (snoc30 g a) B) a
v130 = var30 (vs30 vz30)

v230 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm30 (snoc30 (snoc30 (snoc30 g a) B) C) a
v230 = var30 (vs30 (vs30 vz30))

v330 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm30 (snoc30 (snoc30 (snoc30 (snoc30 g a) B) C) D) a
v330 = var30 (vs30 (vs30 (vs30 vz30)))

v430 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm30 (snoc30 (snoc30 (snoc30 (snoc30 (snoc30 g a) B) C) D) E) a
v430 = var30 (vs30 (vs30 (vs30 (vs30 vz30))))

test30 : {g:_}-> {a:_} -> Tm30 g (arr30 (arr30 a a) (arr30 a a))
test30  = lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030)))))))
Ty31 : Type
Ty31 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty31 : Ty31
empty31 = \ _, empty, _ => empty

arr31 : Ty31 -> Ty31 -> Ty31
arr31 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con31 : Type
Con31 = (Con31 : Type)
 ->(nil  : Con31)
 ->(snoc : Con31 -> Ty31 -> Con31)
 -> Con31

nil31 : Con31
nil31 = \ con, nil31, snoc => nil31

snoc31 : Con31 -> Ty31 -> Con31
snoc31 = \ g, a, con, nil31, snoc31 => snoc31 (g con nil31 snoc31) a

Var31 : Con31 -> Ty31 -> Type
Var31 = \ g, a =>
    (Var31 : Con31 -> Ty31 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var31 (snoc31 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var31 g a -> Var31 (snoc31 g b) a)
 -> Var31 g a

vz31 : {g : _}-> {a : _} -> Var31 (snoc31 g a) a
vz31 = \ var, vz31, vs => vz31 _ _

vs31 : {g : _} -> {B : _} -> {a : _} -> Var31 g a -> Var31 (snoc31 g B) a
vs31 = \ x, var, vz31, vs31 => vs31 _ _ _ (x var vz31 vs31)

Tm31 : Con31 -> Ty31 -> Type
Tm31 = \ g, a =>
    (Tm31    : Con31 -> Ty31 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var31 g a -> Tm31 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm31 (snoc31 g a) B -> Tm31 g (arr31 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm31 g (arr31 a B) -> Tm31 g a -> Tm31 g B)
 -> Tm31 g a

var31 : {g : _} -> {a : _} -> Var31 g a -> Tm31 g a
var31 = \ x, tm, var31, lam, app => var31 _ _ x

lam31 : {g : _} -> {a : _} -> {B : _} -> Tm31 (snoc31 g a) B -> Tm31 g (arr31 a B)
lam31 = \ t, tm, var31, lam31, app => lam31 _ _ _ (t tm var31 lam31 app)

app31 : {g:_}->{a:_}->{B:_} -> Tm31 g (arr31 a B) -> Tm31 g a -> Tm31 g B
app31 = \ t, u, tm, var31, lam31, app31 => app31 _ _ _ (t tm var31 lam31 app31) (u tm var31 lam31 app31)

v031 : {g:_}->{a:_} -> Tm31 (snoc31 g a) a
v031 = var31 vz31

v131 : {g:_}->{a:_}-> {B:_}-> Tm31 (snoc31 (snoc31 g a) B) a
v131 = var31 (vs31 vz31)

v231 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm31 (snoc31 (snoc31 (snoc31 g a) B) C) a
v231 = var31 (vs31 (vs31 vz31))

v331 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm31 (snoc31 (snoc31 (snoc31 (snoc31 g a) B) C) D) a
v331 = var31 (vs31 (vs31 (vs31 vz31)))

v431 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm31 (snoc31 (snoc31 (snoc31 (snoc31 (snoc31 g a) B) C) D) E) a
v431 = var31 (vs31 (vs31 (vs31 (vs31 vz31))))

test31 : {g:_}-> {a:_} -> Tm31 g (arr31 (arr31 a a) (arr31 a a))
test31  = lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031)))))))
Ty32 : Type
Ty32 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty32 : Ty32
empty32 = \ _, empty, _ => empty

arr32 : Ty32 -> Ty32 -> Ty32
arr32 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con32 : Type
Con32 = (Con32 : Type)
 ->(nil  : Con32)
 ->(snoc : Con32 -> Ty32 -> Con32)
 -> Con32

nil32 : Con32
nil32 = \ con, nil32, snoc => nil32

snoc32 : Con32 -> Ty32 -> Con32
snoc32 = \ g, a, con, nil32, snoc32 => snoc32 (g con nil32 snoc32) a

Var32 : Con32 -> Ty32 -> Type
Var32 = \ g, a =>
    (Var32 : Con32 -> Ty32 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var32 (snoc32 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var32 g a -> Var32 (snoc32 g b) a)
 -> Var32 g a

vz32 : {g : _}-> {a : _} -> Var32 (snoc32 g a) a
vz32 = \ var, vz32, vs => vz32 _ _

vs32 : {g : _} -> {B : _} -> {a : _} -> Var32 g a -> Var32 (snoc32 g B) a
vs32 = \ x, var, vz32, vs32 => vs32 _ _ _ (x var vz32 vs32)

Tm32 : Con32 -> Ty32 -> Type
Tm32 = \ g, a =>
    (Tm32    : Con32 -> Ty32 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var32 g a -> Tm32 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm32 (snoc32 g a) B -> Tm32 g (arr32 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm32 g (arr32 a B) -> Tm32 g a -> Tm32 g B)
 -> Tm32 g a

var32 : {g : _} -> {a : _} -> Var32 g a -> Tm32 g a
var32 = \ x, tm, var32, lam, app => var32 _ _ x

lam32 : {g : _} -> {a : _} -> {B : _} -> Tm32 (snoc32 g a) B -> Tm32 g (arr32 a B)
lam32 = \ t, tm, var32, lam32, app => lam32 _ _ _ (t tm var32 lam32 app)

app32 : {g:_}->{a:_}->{B:_} -> Tm32 g (arr32 a B) -> Tm32 g a -> Tm32 g B
app32 = \ t, u, tm, var32, lam32, app32 => app32 _ _ _ (t tm var32 lam32 app32) (u tm var32 lam32 app32)

v032 : {g:_}->{a:_} -> Tm32 (snoc32 g a) a
v032 = var32 vz32

v132 : {g:_}->{a:_}-> {B:_}-> Tm32 (snoc32 (snoc32 g a) B) a
v132 = var32 (vs32 vz32)

v232 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm32 (snoc32 (snoc32 (snoc32 g a) B) C) a
v232 = var32 (vs32 (vs32 vz32))

v332 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm32 (snoc32 (snoc32 (snoc32 (snoc32 g a) B) C) D) a
v332 = var32 (vs32 (vs32 (vs32 vz32)))

v432 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm32 (snoc32 (snoc32 (snoc32 (snoc32 (snoc32 g a) B) C) D) E) a
v432 = var32 (vs32 (vs32 (vs32 (vs32 vz32))))

test32 : {g:_}-> {a:_} -> Tm32 g (arr32 (arr32 a a) (arr32 a a))
test32  = lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032)))))))
Ty33 : Type
Ty33 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty33 : Ty33
empty33 = \ _, empty, _ => empty

arr33 : Ty33 -> Ty33 -> Ty33
arr33 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con33 : Type
Con33 = (Con33 : Type)
 ->(nil  : Con33)
 ->(snoc : Con33 -> Ty33 -> Con33)
 -> Con33

nil33 : Con33
nil33 = \ con, nil33, snoc => nil33

snoc33 : Con33 -> Ty33 -> Con33
snoc33 = \ g, a, con, nil33, snoc33 => snoc33 (g con nil33 snoc33) a

Var33 : Con33 -> Ty33 -> Type
Var33 = \ g, a =>
    (Var33 : Con33 -> Ty33 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var33 (snoc33 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var33 g a -> Var33 (snoc33 g b) a)
 -> Var33 g a

vz33 : {g : _}-> {a : _} -> Var33 (snoc33 g a) a
vz33 = \ var, vz33, vs => vz33 _ _

vs33 : {g : _} -> {B : _} -> {a : _} -> Var33 g a -> Var33 (snoc33 g B) a
vs33 = \ x, var, vz33, vs33 => vs33 _ _ _ (x var vz33 vs33)

Tm33 : Con33 -> Ty33 -> Type
Tm33 = \ g, a =>
    (Tm33    : Con33 -> Ty33 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var33 g a -> Tm33 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm33 (snoc33 g a) B -> Tm33 g (arr33 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm33 g (arr33 a B) -> Tm33 g a -> Tm33 g B)
 -> Tm33 g a

var33 : {g : _} -> {a : _} -> Var33 g a -> Tm33 g a
var33 = \ x, tm, var33, lam, app => var33 _ _ x

lam33 : {g : _} -> {a : _} -> {B : _} -> Tm33 (snoc33 g a) B -> Tm33 g (arr33 a B)
lam33 = \ t, tm, var33, lam33, app => lam33 _ _ _ (t tm var33 lam33 app)

app33 : {g:_}->{a:_}->{B:_} -> Tm33 g (arr33 a B) -> Tm33 g a -> Tm33 g B
app33 = \ t, u, tm, var33, lam33, app33 => app33 _ _ _ (t tm var33 lam33 app33) (u tm var33 lam33 app33)

v033 : {g:_}->{a:_} -> Tm33 (snoc33 g a) a
v033 = var33 vz33

v133 : {g:_}->{a:_}-> {B:_}-> Tm33 (snoc33 (snoc33 g a) B) a
v133 = var33 (vs33 vz33)

v233 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm33 (snoc33 (snoc33 (snoc33 g a) B) C) a
v233 = var33 (vs33 (vs33 vz33))

v333 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm33 (snoc33 (snoc33 (snoc33 (snoc33 g a) B) C) D) a
v333 = var33 (vs33 (vs33 (vs33 vz33)))

v433 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm33 (snoc33 (snoc33 (snoc33 (snoc33 (snoc33 g a) B) C) D) E) a
v433 = var33 (vs33 (vs33 (vs33 (vs33 vz33))))

test33 : {g:_}-> {a:_} -> Tm33 g (arr33 (arr33 a a) (arr33 a a))
test33  = lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033)))))))
Ty34 : Type
Ty34 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty34 : Ty34
empty34 = \ _, empty, _ => empty

arr34 : Ty34 -> Ty34 -> Ty34
arr34 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con34 : Type
Con34 = (Con34 : Type)
 ->(nil  : Con34)
 ->(snoc : Con34 -> Ty34 -> Con34)
 -> Con34

nil34 : Con34
nil34 = \ con, nil34, snoc => nil34

snoc34 : Con34 -> Ty34 -> Con34
snoc34 = \ g, a, con, nil34, snoc34 => snoc34 (g con nil34 snoc34) a

Var34 : Con34 -> Ty34 -> Type
Var34 = \ g, a =>
    (Var34 : Con34 -> Ty34 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var34 (snoc34 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var34 g a -> Var34 (snoc34 g b) a)
 -> Var34 g a

vz34 : {g : _}-> {a : _} -> Var34 (snoc34 g a) a
vz34 = \ var, vz34, vs => vz34 _ _

vs34 : {g : _} -> {B : _} -> {a : _} -> Var34 g a -> Var34 (snoc34 g B) a
vs34 = \ x, var, vz34, vs34 => vs34 _ _ _ (x var vz34 vs34)

Tm34 : Con34 -> Ty34 -> Type
Tm34 = \ g, a =>
    (Tm34    : Con34 -> Ty34 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var34 g a -> Tm34 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm34 (snoc34 g a) B -> Tm34 g (arr34 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm34 g (arr34 a B) -> Tm34 g a -> Tm34 g B)
 -> Tm34 g a

var34 : {g : _} -> {a : _} -> Var34 g a -> Tm34 g a
var34 = \ x, tm, var34, lam, app => var34 _ _ x

lam34 : {g : _} -> {a : _} -> {B : _} -> Tm34 (snoc34 g a) B -> Tm34 g (arr34 a B)
lam34 = \ t, tm, var34, lam34, app => lam34 _ _ _ (t tm var34 lam34 app)

app34 : {g:_}->{a:_}->{B:_} -> Tm34 g (arr34 a B) -> Tm34 g a -> Tm34 g B
app34 = \ t, u, tm, var34, lam34, app34 => app34 _ _ _ (t tm var34 lam34 app34) (u tm var34 lam34 app34)

v034 : {g:_}->{a:_} -> Tm34 (snoc34 g a) a
v034 = var34 vz34

v134 : {g:_}->{a:_}-> {B:_}-> Tm34 (snoc34 (snoc34 g a) B) a
v134 = var34 (vs34 vz34)

v234 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm34 (snoc34 (snoc34 (snoc34 g a) B) C) a
v234 = var34 (vs34 (vs34 vz34))

v334 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm34 (snoc34 (snoc34 (snoc34 (snoc34 g a) B) C) D) a
v334 = var34 (vs34 (vs34 (vs34 vz34)))

v434 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm34 (snoc34 (snoc34 (snoc34 (snoc34 (snoc34 g a) B) C) D) E) a
v434 = var34 (vs34 (vs34 (vs34 (vs34 vz34))))

test34 : {g:_}-> {a:_} -> Tm34 g (arr34 (arr34 a a) (arr34 a a))
test34  = lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034)))))))
Ty35 : Type
Ty35 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty35 : Ty35
empty35 = \ _, empty, _ => empty

arr35 : Ty35 -> Ty35 -> Ty35
arr35 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con35 : Type
Con35 = (Con35 : Type)
 ->(nil  : Con35)
 ->(snoc : Con35 -> Ty35 -> Con35)
 -> Con35

nil35 : Con35
nil35 = \ con, nil35, snoc => nil35

snoc35 : Con35 -> Ty35 -> Con35
snoc35 = \ g, a, con, nil35, snoc35 => snoc35 (g con nil35 snoc35) a

Var35 : Con35 -> Ty35 -> Type
Var35 = \ g, a =>
    (Var35 : Con35 -> Ty35 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var35 (snoc35 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var35 g a -> Var35 (snoc35 g b) a)
 -> Var35 g a

vz35 : {g : _}-> {a : _} -> Var35 (snoc35 g a) a
vz35 = \ var, vz35, vs => vz35 _ _

vs35 : {g : _} -> {B : _} -> {a : _} -> Var35 g a -> Var35 (snoc35 g B) a
vs35 = \ x, var, vz35, vs35 => vs35 _ _ _ (x var vz35 vs35)

Tm35 : Con35 -> Ty35 -> Type
Tm35 = \ g, a =>
    (Tm35    : Con35 -> Ty35 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var35 g a -> Tm35 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm35 (snoc35 g a) B -> Tm35 g (arr35 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm35 g (arr35 a B) -> Tm35 g a -> Tm35 g B)
 -> Tm35 g a

var35 : {g : _} -> {a : _} -> Var35 g a -> Tm35 g a
var35 = \ x, tm, var35, lam, app => var35 _ _ x

lam35 : {g : _} -> {a : _} -> {B : _} -> Tm35 (snoc35 g a) B -> Tm35 g (arr35 a B)
lam35 = \ t, tm, var35, lam35, app => lam35 _ _ _ (t tm var35 lam35 app)

app35 : {g:_}->{a:_}->{B:_} -> Tm35 g (arr35 a B) -> Tm35 g a -> Tm35 g B
app35 = \ t, u, tm, var35, lam35, app35 => app35 _ _ _ (t tm var35 lam35 app35) (u tm var35 lam35 app35)

v035 : {g:_}->{a:_} -> Tm35 (snoc35 g a) a
v035 = var35 vz35

v135 : {g:_}->{a:_}-> {B:_}-> Tm35 (snoc35 (snoc35 g a) B) a
v135 = var35 (vs35 vz35)

v235 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm35 (snoc35 (snoc35 (snoc35 g a) B) C) a
v235 = var35 (vs35 (vs35 vz35))

v335 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm35 (snoc35 (snoc35 (snoc35 (snoc35 g a) B) C) D) a
v335 = var35 (vs35 (vs35 (vs35 vz35)))

v435 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm35 (snoc35 (snoc35 (snoc35 (snoc35 (snoc35 g a) B) C) D) E) a
v435 = var35 (vs35 (vs35 (vs35 (vs35 vz35))))

test35 : {g:_}-> {a:_} -> Tm35 g (arr35 (arr35 a a) (arr35 a a))
test35  = lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035)))))))
Ty36 : Type
Ty36 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty36 : Ty36
empty36 = \ _, empty, _ => empty

arr36 : Ty36 -> Ty36 -> Ty36
arr36 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con36 : Type
Con36 = (Con36 : Type)
 ->(nil  : Con36)
 ->(snoc : Con36 -> Ty36 -> Con36)
 -> Con36

nil36 : Con36
nil36 = \ con, nil36, snoc => nil36

snoc36 : Con36 -> Ty36 -> Con36
snoc36 = \ g, a, con, nil36, snoc36 => snoc36 (g con nil36 snoc36) a

Var36 : Con36 -> Ty36 -> Type
Var36 = \ g, a =>
    (Var36 : Con36 -> Ty36 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var36 (snoc36 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var36 g a -> Var36 (snoc36 g b) a)
 -> Var36 g a

vz36 : {g : _}-> {a : _} -> Var36 (snoc36 g a) a
vz36 = \ var, vz36, vs => vz36 _ _

vs36 : {g : _} -> {B : _} -> {a : _} -> Var36 g a -> Var36 (snoc36 g B) a
vs36 = \ x, var, vz36, vs36 => vs36 _ _ _ (x var vz36 vs36)

Tm36 : Con36 -> Ty36 -> Type
Tm36 = \ g, a =>
    (Tm36    : Con36 -> Ty36 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var36 g a -> Tm36 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm36 (snoc36 g a) B -> Tm36 g (arr36 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm36 g (arr36 a B) -> Tm36 g a -> Tm36 g B)
 -> Tm36 g a

var36 : {g : _} -> {a : _} -> Var36 g a -> Tm36 g a
var36 = \ x, tm, var36, lam, app => var36 _ _ x

lam36 : {g : _} -> {a : _} -> {B : _} -> Tm36 (snoc36 g a) B -> Tm36 g (arr36 a B)
lam36 = \ t, tm, var36, lam36, app => lam36 _ _ _ (t tm var36 lam36 app)

app36 : {g:_}->{a:_}->{B:_} -> Tm36 g (arr36 a B) -> Tm36 g a -> Tm36 g B
app36 = \ t, u, tm, var36, lam36, app36 => app36 _ _ _ (t tm var36 lam36 app36) (u tm var36 lam36 app36)

v036 : {g:_}->{a:_} -> Tm36 (snoc36 g a) a
v036 = var36 vz36

v136 : {g:_}->{a:_}-> {B:_}-> Tm36 (snoc36 (snoc36 g a) B) a
v136 = var36 (vs36 vz36)

v236 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm36 (snoc36 (snoc36 (snoc36 g a) B) C) a
v236 = var36 (vs36 (vs36 vz36))

v336 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm36 (snoc36 (snoc36 (snoc36 (snoc36 g a) B) C) D) a
v336 = var36 (vs36 (vs36 (vs36 vz36)))

v436 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm36 (snoc36 (snoc36 (snoc36 (snoc36 (snoc36 g a) B) C) D) E) a
v436 = var36 (vs36 (vs36 (vs36 (vs36 vz36))))

test36 : {g:_}-> {a:_} -> Tm36 g (arr36 (arr36 a a) (arr36 a a))
test36  = lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036)))))))
Ty37 : Type
Ty37 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty37 : Ty37
empty37 = \ _, empty, _ => empty

arr37 : Ty37 -> Ty37 -> Ty37
arr37 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con37 : Type
Con37 = (Con37 : Type)
 ->(nil  : Con37)
 ->(snoc : Con37 -> Ty37 -> Con37)
 -> Con37

nil37 : Con37
nil37 = \ con, nil37, snoc => nil37

snoc37 : Con37 -> Ty37 -> Con37
snoc37 = \ g, a, con, nil37, snoc37 => snoc37 (g con nil37 snoc37) a

Var37 : Con37 -> Ty37 -> Type
Var37 = \ g, a =>
    (Var37 : Con37 -> Ty37 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var37 (snoc37 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var37 g a -> Var37 (snoc37 g b) a)
 -> Var37 g a

vz37 : {g : _}-> {a : _} -> Var37 (snoc37 g a) a
vz37 = \ var, vz37, vs => vz37 _ _

vs37 : {g : _} -> {B : _} -> {a : _} -> Var37 g a -> Var37 (snoc37 g B) a
vs37 = \ x, var, vz37, vs37 => vs37 _ _ _ (x var vz37 vs37)

Tm37 : Con37 -> Ty37 -> Type
Tm37 = \ g, a =>
    (Tm37    : Con37 -> Ty37 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var37 g a -> Tm37 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm37 (snoc37 g a) B -> Tm37 g (arr37 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm37 g (arr37 a B) -> Tm37 g a -> Tm37 g B)
 -> Tm37 g a

var37 : {g : _} -> {a : _} -> Var37 g a -> Tm37 g a
var37 = \ x, tm, var37, lam, app => var37 _ _ x

lam37 : {g : _} -> {a : _} -> {B : _} -> Tm37 (snoc37 g a) B -> Tm37 g (arr37 a B)
lam37 = \ t, tm, var37, lam37, app => lam37 _ _ _ (t tm var37 lam37 app)

app37 : {g:_}->{a:_}->{B:_} -> Tm37 g (arr37 a B) -> Tm37 g a -> Tm37 g B
app37 = \ t, u, tm, var37, lam37, app37 => app37 _ _ _ (t tm var37 lam37 app37) (u tm var37 lam37 app37)

v037 : {g:_}->{a:_} -> Tm37 (snoc37 g a) a
v037 = var37 vz37

v137 : {g:_}->{a:_}-> {B:_}-> Tm37 (snoc37 (snoc37 g a) B) a
v137 = var37 (vs37 vz37)

v237 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm37 (snoc37 (snoc37 (snoc37 g a) B) C) a
v237 = var37 (vs37 (vs37 vz37))

v337 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm37 (snoc37 (snoc37 (snoc37 (snoc37 g a) B) C) D) a
v337 = var37 (vs37 (vs37 (vs37 vz37)))

v437 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm37 (snoc37 (snoc37 (snoc37 (snoc37 (snoc37 g a) B) C) D) E) a
v437 = var37 (vs37 (vs37 (vs37 (vs37 vz37))))

test37 : {g:_}-> {a:_} -> Tm37 g (arr37 (arr37 a a) (arr37 a a))
test37  = lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037)))))))
Ty38 : Type
Ty38 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty38 : Ty38
empty38 = \ _, empty, _ => empty

arr38 : Ty38 -> Ty38 -> Ty38
arr38 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con38 : Type
Con38 = (Con38 : Type)
 ->(nil  : Con38)
 ->(snoc : Con38 -> Ty38 -> Con38)
 -> Con38

nil38 : Con38
nil38 = \ con, nil38, snoc => nil38

snoc38 : Con38 -> Ty38 -> Con38
snoc38 = \ g, a, con, nil38, snoc38 => snoc38 (g con nil38 snoc38) a

Var38 : Con38 -> Ty38 -> Type
Var38 = \ g, a =>
    (Var38 : Con38 -> Ty38 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var38 (snoc38 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var38 g a -> Var38 (snoc38 g b) a)
 -> Var38 g a

vz38 : {g : _}-> {a : _} -> Var38 (snoc38 g a) a
vz38 = \ var, vz38, vs => vz38 _ _

vs38 : {g : _} -> {B : _} -> {a : _} -> Var38 g a -> Var38 (snoc38 g B) a
vs38 = \ x, var, vz38, vs38 => vs38 _ _ _ (x var vz38 vs38)

Tm38 : Con38 -> Ty38 -> Type
Tm38 = \ g, a =>
    (Tm38    : Con38 -> Ty38 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var38 g a -> Tm38 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm38 (snoc38 g a) B -> Tm38 g (arr38 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm38 g (arr38 a B) -> Tm38 g a -> Tm38 g B)
 -> Tm38 g a

var38 : {g : _} -> {a : _} -> Var38 g a -> Tm38 g a
var38 = \ x, tm, var38, lam, app => var38 _ _ x

lam38 : {g : _} -> {a : _} -> {B : _} -> Tm38 (snoc38 g a) B -> Tm38 g (arr38 a B)
lam38 = \ t, tm, var38, lam38, app => lam38 _ _ _ (t tm var38 lam38 app)

app38 : {g:_}->{a:_}->{B:_} -> Tm38 g (arr38 a B) -> Tm38 g a -> Tm38 g B
app38 = \ t, u, tm, var38, lam38, app38 => app38 _ _ _ (t tm var38 lam38 app38) (u tm var38 lam38 app38)

v038 : {g:_}->{a:_} -> Tm38 (snoc38 g a) a
v038 = var38 vz38

v138 : {g:_}->{a:_}-> {B:_}-> Tm38 (snoc38 (snoc38 g a) B) a
v138 = var38 (vs38 vz38)

v238 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm38 (snoc38 (snoc38 (snoc38 g a) B) C) a
v238 = var38 (vs38 (vs38 vz38))

v338 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm38 (snoc38 (snoc38 (snoc38 (snoc38 g a) B) C) D) a
v338 = var38 (vs38 (vs38 (vs38 vz38)))

v438 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm38 (snoc38 (snoc38 (snoc38 (snoc38 (snoc38 g a) B) C) D) E) a
v438 = var38 (vs38 (vs38 (vs38 (vs38 vz38))))

test38 : {g:_}-> {a:_} -> Tm38 g (arr38 (arr38 a a) (arr38 a a))
test38  = lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038)))))))
Ty39 : Type
Ty39 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty39 : Ty39
empty39 = \ _, empty, _ => empty

arr39 : Ty39 -> Ty39 -> Ty39
arr39 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con39 : Type
Con39 = (Con39 : Type)
 ->(nil  : Con39)
 ->(snoc : Con39 -> Ty39 -> Con39)
 -> Con39

nil39 : Con39
nil39 = \ con, nil39, snoc => nil39

snoc39 : Con39 -> Ty39 -> Con39
snoc39 = \ g, a, con, nil39, snoc39 => snoc39 (g con nil39 snoc39) a

Var39 : Con39 -> Ty39 -> Type
Var39 = \ g, a =>
    (Var39 : Con39 -> Ty39 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var39 (snoc39 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var39 g a -> Var39 (snoc39 g b) a)
 -> Var39 g a

vz39 : {g : _}-> {a : _} -> Var39 (snoc39 g a) a
vz39 = \ var, vz39, vs => vz39 _ _

vs39 : {g : _} -> {B : _} -> {a : _} -> Var39 g a -> Var39 (snoc39 g B) a
vs39 = \ x, var, vz39, vs39 => vs39 _ _ _ (x var vz39 vs39)

Tm39 : Con39 -> Ty39 -> Type
Tm39 = \ g, a =>
    (Tm39    : Con39 -> Ty39 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var39 g a -> Tm39 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm39 (snoc39 g a) B -> Tm39 g (arr39 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm39 g (arr39 a B) -> Tm39 g a -> Tm39 g B)
 -> Tm39 g a

var39 : {g : _} -> {a : _} -> Var39 g a -> Tm39 g a
var39 = \ x, tm, var39, lam, app => var39 _ _ x

lam39 : {g : _} -> {a : _} -> {B : _} -> Tm39 (snoc39 g a) B -> Tm39 g (arr39 a B)
lam39 = \ t, tm, var39, lam39, app => lam39 _ _ _ (t tm var39 lam39 app)

app39 : {g:_}->{a:_}->{B:_} -> Tm39 g (arr39 a B) -> Tm39 g a -> Tm39 g B
app39 = \ t, u, tm, var39, lam39, app39 => app39 _ _ _ (t tm var39 lam39 app39) (u tm var39 lam39 app39)

v039 : {g:_}->{a:_} -> Tm39 (snoc39 g a) a
v039 = var39 vz39

v139 : {g:_}->{a:_}-> {B:_}-> Tm39 (snoc39 (snoc39 g a) B) a
v139 = var39 (vs39 vz39)

v239 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm39 (snoc39 (snoc39 (snoc39 g a) B) C) a
v239 = var39 (vs39 (vs39 vz39))

v339 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm39 (snoc39 (snoc39 (snoc39 (snoc39 g a) B) C) D) a
v339 = var39 (vs39 (vs39 (vs39 vz39)))

v439 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm39 (snoc39 (snoc39 (snoc39 (snoc39 (snoc39 g a) B) C) D) E) a
v439 = var39 (vs39 (vs39 (vs39 (vs39 vz39))))

test39 : {g:_}-> {a:_} -> Tm39 g (arr39 (arr39 a a) (arr39 a a))
test39  = lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039)))))))
Ty40 : Type
Ty40 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty40 : Ty40
empty40 = \ _, empty, _ => empty

arr40 : Ty40 -> Ty40 -> Ty40
arr40 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con40 : Type
Con40 = (Con40 : Type)
 ->(nil  : Con40)
 ->(snoc : Con40 -> Ty40 -> Con40)
 -> Con40

nil40 : Con40
nil40 = \ con, nil40, snoc => nil40

snoc40 : Con40 -> Ty40 -> Con40
snoc40 = \ g, a, con, nil40, snoc40 => snoc40 (g con nil40 snoc40) a

Var40 : Con40 -> Ty40 -> Type
Var40 = \ g, a =>
    (Var40 : Con40 -> Ty40 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var40 (snoc40 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var40 g a -> Var40 (snoc40 g b) a)
 -> Var40 g a

vz40 : {g : _}-> {a : _} -> Var40 (snoc40 g a) a
vz40 = \ var, vz40, vs => vz40 _ _

vs40 : {g : _} -> {B : _} -> {a : _} -> Var40 g a -> Var40 (snoc40 g B) a
vs40 = \ x, var, vz40, vs40 => vs40 _ _ _ (x var vz40 vs40)

Tm40 : Con40 -> Ty40 -> Type
Tm40 = \ g, a =>
    (Tm40    : Con40 -> Ty40 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var40 g a -> Tm40 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm40 (snoc40 g a) B -> Tm40 g (arr40 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm40 g (arr40 a B) -> Tm40 g a -> Tm40 g B)
 -> Tm40 g a

var40 : {g : _} -> {a : _} -> Var40 g a -> Tm40 g a
var40 = \ x, tm, var40, lam, app => var40 _ _ x

lam40 : {g : _} -> {a : _} -> {B : _} -> Tm40 (snoc40 g a) B -> Tm40 g (arr40 a B)
lam40 = \ t, tm, var40, lam40, app => lam40 _ _ _ (t tm var40 lam40 app)

app40 : {g:_}->{a:_}->{B:_} -> Tm40 g (arr40 a B) -> Tm40 g a -> Tm40 g B
app40 = \ t, u, tm, var40, lam40, app40 => app40 _ _ _ (t tm var40 lam40 app40) (u tm var40 lam40 app40)

v040 : {g:_}->{a:_} -> Tm40 (snoc40 g a) a
v040 = var40 vz40

v140 : {g:_}->{a:_}-> {B:_}-> Tm40 (snoc40 (snoc40 g a) B) a
v140 = var40 (vs40 vz40)

v240 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm40 (snoc40 (snoc40 (snoc40 g a) B) C) a
v240 = var40 (vs40 (vs40 vz40))

v340 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm40 (snoc40 (snoc40 (snoc40 (snoc40 g a) B) C) D) a
v340 = var40 (vs40 (vs40 (vs40 vz40)))

v440 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm40 (snoc40 (snoc40 (snoc40 (snoc40 (snoc40 g a) B) C) D) E) a
v440 = var40 (vs40 (vs40 (vs40 (vs40 vz40))))

test40 : {g:_}-> {a:_} -> Tm40 g (arr40 (arr40 a a) (arr40 a a))
test40  = lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040)))))))
Ty41 : Type
Ty41 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty41 : Ty41
empty41 = \ _, empty, _ => empty

arr41 : Ty41 -> Ty41 -> Ty41
arr41 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con41 : Type
Con41 = (Con41 : Type)
 ->(nil  : Con41)
 ->(snoc : Con41 -> Ty41 -> Con41)
 -> Con41

nil41 : Con41
nil41 = \ con, nil41, snoc => nil41

snoc41 : Con41 -> Ty41 -> Con41
snoc41 = \ g, a, con, nil41, snoc41 => snoc41 (g con nil41 snoc41) a

Var41 : Con41 -> Ty41 -> Type
Var41 = \ g, a =>
    (Var41 : Con41 -> Ty41 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var41 (snoc41 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var41 g a -> Var41 (snoc41 g b) a)
 -> Var41 g a

vz41 : {g : _}-> {a : _} -> Var41 (snoc41 g a) a
vz41 = \ var, vz41, vs => vz41 _ _

vs41 : {g : _} -> {B : _} -> {a : _} -> Var41 g a -> Var41 (snoc41 g B) a
vs41 = \ x, var, vz41, vs41 => vs41 _ _ _ (x var vz41 vs41)

Tm41 : Con41 -> Ty41 -> Type
Tm41 = \ g, a =>
    (Tm41    : Con41 -> Ty41 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var41 g a -> Tm41 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm41 (snoc41 g a) B -> Tm41 g (arr41 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm41 g (arr41 a B) -> Tm41 g a -> Tm41 g B)
 -> Tm41 g a

var41 : {g : _} -> {a : _} -> Var41 g a -> Tm41 g a
var41 = \ x, tm, var41, lam, app => var41 _ _ x

lam41 : {g : _} -> {a : _} -> {B : _} -> Tm41 (snoc41 g a) B -> Tm41 g (arr41 a B)
lam41 = \ t, tm, var41, lam41, app => lam41 _ _ _ (t tm var41 lam41 app)

app41 : {g:_}->{a:_}->{B:_} -> Tm41 g (arr41 a B) -> Tm41 g a -> Tm41 g B
app41 = \ t, u, tm, var41, lam41, app41 => app41 _ _ _ (t tm var41 lam41 app41) (u tm var41 lam41 app41)

v041 : {g:_}->{a:_} -> Tm41 (snoc41 g a) a
v041 = var41 vz41

v141 : {g:_}->{a:_}-> {B:_}-> Tm41 (snoc41 (snoc41 g a) B) a
v141 = var41 (vs41 vz41)

v241 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm41 (snoc41 (snoc41 (snoc41 g a) B) C) a
v241 = var41 (vs41 (vs41 vz41))

v341 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm41 (snoc41 (snoc41 (snoc41 (snoc41 g a) B) C) D) a
v341 = var41 (vs41 (vs41 (vs41 vz41)))

v441 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm41 (snoc41 (snoc41 (snoc41 (snoc41 (snoc41 g a) B) C) D) E) a
v441 = var41 (vs41 (vs41 (vs41 (vs41 vz41))))

test41 : {g:_}-> {a:_} -> Tm41 g (arr41 (arr41 a a) (arr41 a a))
test41  = lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041)))))))
Ty42 : Type
Ty42 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty42 : Ty42
empty42 = \ _, empty, _ => empty

arr42 : Ty42 -> Ty42 -> Ty42
arr42 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con42 : Type
Con42 = (Con42 : Type)
 ->(nil  : Con42)
 ->(snoc : Con42 -> Ty42 -> Con42)
 -> Con42

nil42 : Con42
nil42 = \ con, nil42, snoc => nil42

snoc42 : Con42 -> Ty42 -> Con42
snoc42 = \ g, a, con, nil42, snoc42 => snoc42 (g con nil42 snoc42) a

Var42 : Con42 -> Ty42 -> Type
Var42 = \ g, a =>
    (Var42 : Con42 -> Ty42 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var42 (snoc42 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var42 g a -> Var42 (snoc42 g b) a)
 -> Var42 g a

vz42 : {g : _}-> {a : _} -> Var42 (snoc42 g a) a
vz42 = \ var, vz42, vs => vz42 _ _

vs42 : {g : _} -> {B : _} -> {a : _} -> Var42 g a -> Var42 (snoc42 g B) a
vs42 = \ x, var, vz42, vs42 => vs42 _ _ _ (x var vz42 vs42)

Tm42 : Con42 -> Ty42 -> Type
Tm42 = \ g, a =>
    (Tm42    : Con42 -> Ty42 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var42 g a -> Tm42 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm42 (snoc42 g a) B -> Tm42 g (arr42 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm42 g (arr42 a B) -> Tm42 g a -> Tm42 g B)
 -> Tm42 g a

var42 : {g : _} -> {a : _} -> Var42 g a -> Tm42 g a
var42 = \ x, tm, var42, lam, app => var42 _ _ x

lam42 : {g : _} -> {a : _} -> {B : _} -> Tm42 (snoc42 g a) B -> Tm42 g (arr42 a B)
lam42 = \ t, tm, var42, lam42, app => lam42 _ _ _ (t tm var42 lam42 app)

app42 : {g:_}->{a:_}->{B:_} -> Tm42 g (arr42 a B) -> Tm42 g a -> Tm42 g B
app42 = \ t, u, tm, var42, lam42, app42 => app42 _ _ _ (t tm var42 lam42 app42) (u tm var42 lam42 app42)

v042 : {g:_}->{a:_} -> Tm42 (snoc42 g a) a
v042 = var42 vz42

v142 : {g:_}->{a:_}-> {B:_}-> Tm42 (snoc42 (snoc42 g a) B) a
v142 = var42 (vs42 vz42)

v242 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm42 (snoc42 (snoc42 (snoc42 g a) B) C) a
v242 = var42 (vs42 (vs42 vz42))

v342 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm42 (snoc42 (snoc42 (snoc42 (snoc42 g a) B) C) D) a
v342 = var42 (vs42 (vs42 (vs42 vz42)))

v442 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm42 (snoc42 (snoc42 (snoc42 (snoc42 (snoc42 g a) B) C) D) E) a
v442 = var42 (vs42 (vs42 (vs42 (vs42 vz42))))

test42 : {g:_}-> {a:_} -> Tm42 g (arr42 (arr42 a a) (arr42 a a))
test42  = lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042)))))))
Ty43 : Type
Ty43 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty43 : Ty43
empty43 = \ _, empty, _ => empty

arr43 : Ty43 -> Ty43 -> Ty43
arr43 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con43 : Type
Con43 = (Con43 : Type)
 ->(nil  : Con43)
 ->(snoc : Con43 -> Ty43 -> Con43)
 -> Con43

nil43 : Con43
nil43 = \ con, nil43, snoc => nil43

snoc43 : Con43 -> Ty43 -> Con43
snoc43 = \ g, a, con, nil43, snoc43 => snoc43 (g con nil43 snoc43) a

Var43 : Con43 -> Ty43 -> Type
Var43 = \ g, a =>
    (Var43 : Con43 -> Ty43 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var43 (snoc43 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var43 g a -> Var43 (snoc43 g b) a)
 -> Var43 g a

vz43 : {g : _}-> {a : _} -> Var43 (snoc43 g a) a
vz43 = \ var, vz43, vs => vz43 _ _

vs43 : {g : _} -> {B : _} -> {a : _} -> Var43 g a -> Var43 (snoc43 g B) a
vs43 = \ x, var, vz43, vs43 => vs43 _ _ _ (x var vz43 vs43)

Tm43 : Con43 -> Ty43 -> Type
Tm43 = \ g, a =>
    (Tm43    : Con43 -> Ty43 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var43 g a -> Tm43 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm43 (snoc43 g a) B -> Tm43 g (arr43 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm43 g (arr43 a B) -> Tm43 g a -> Tm43 g B)
 -> Tm43 g a

var43 : {g : _} -> {a : _} -> Var43 g a -> Tm43 g a
var43 = \ x, tm, var43, lam, app => var43 _ _ x

lam43 : {g : _} -> {a : _} -> {B : _} -> Tm43 (snoc43 g a) B -> Tm43 g (arr43 a B)
lam43 = \ t, tm, var43, lam43, app => lam43 _ _ _ (t tm var43 lam43 app)

app43 : {g:_}->{a:_}->{B:_} -> Tm43 g (arr43 a B) -> Tm43 g a -> Tm43 g B
app43 = \ t, u, tm, var43, lam43, app43 => app43 _ _ _ (t tm var43 lam43 app43) (u tm var43 lam43 app43)

v043 : {g:_}->{a:_} -> Tm43 (snoc43 g a) a
v043 = var43 vz43

v143 : {g:_}->{a:_}-> {B:_}-> Tm43 (snoc43 (snoc43 g a) B) a
v143 = var43 (vs43 vz43)

v243 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm43 (snoc43 (snoc43 (snoc43 g a) B) C) a
v243 = var43 (vs43 (vs43 vz43))

v343 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm43 (snoc43 (snoc43 (snoc43 (snoc43 g a) B) C) D) a
v343 = var43 (vs43 (vs43 (vs43 vz43)))

v443 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm43 (snoc43 (snoc43 (snoc43 (snoc43 (snoc43 g a) B) C) D) E) a
v443 = var43 (vs43 (vs43 (vs43 (vs43 vz43))))

test43 : {g:_}-> {a:_} -> Tm43 g (arr43 (arr43 a a) (arr43 a a))
test43  = lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043)))))))
Ty44 : Type
Ty44 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty44 : Ty44
empty44 = \ _, empty, _ => empty

arr44 : Ty44 -> Ty44 -> Ty44
arr44 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con44 : Type
Con44 = (Con44 : Type)
 ->(nil  : Con44)
 ->(snoc : Con44 -> Ty44 -> Con44)
 -> Con44

nil44 : Con44
nil44 = \ con, nil44, snoc => nil44

snoc44 : Con44 -> Ty44 -> Con44
snoc44 = \ g, a, con, nil44, snoc44 => snoc44 (g con nil44 snoc44) a

Var44 : Con44 -> Ty44 -> Type
Var44 = \ g, a =>
    (Var44 : Con44 -> Ty44 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var44 (snoc44 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var44 g a -> Var44 (snoc44 g b) a)
 -> Var44 g a

vz44 : {g : _}-> {a : _} -> Var44 (snoc44 g a) a
vz44 = \ var, vz44, vs => vz44 _ _

vs44 : {g : _} -> {B : _} -> {a : _} -> Var44 g a -> Var44 (snoc44 g B) a
vs44 = \ x, var, vz44, vs44 => vs44 _ _ _ (x var vz44 vs44)

Tm44 : Con44 -> Ty44 -> Type
Tm44 = \ g, a =>
    (Tm44    : Con44 -> Ty44 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var44 g a -> Tm44 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm44 (snoc44 g a) B -> Tm44 g (arr44 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm44 g (arr44 a B) -> Tm44 g a -> Tm44 g B)
 -> Tm44 g a

var44 : {g : _} -> {a : _} -> Var44 g a -> Tm44 g a
var44 = \ x, tm, var44, lam, app => var44 _ _ x

lam44 : {g : _} -> {a : _} -> {B : _} -> Tm44 (snoc44 g a) B -> Tm44 g (arr44 a B)
lam44 = \ t, tm, var44, lam44, app => lam44 _ _ _ (t tm var44 lam44 app)

app44 : {g:_}->{a:_}->{B:_} -> Tm44 g (arr44 a B) -> Tm44 g a -> Tm44 g B
app44 = \ t, u, tm, var44, lam44, app44 => app44 _ _ _ (t tm var44 lam44 app44) (u tm var44 lam44 app44)

v044 : {g:_}->{a:_} -> Tm44 (snoc44 g a) a
v044 = var44 vz44

v144 : {g:_}->{a:_}-> {B:_}-> Tm44 (snoc44 (snoc44 g a) B) a
v144 = var44 (vs44 vz44)

v244 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm44 (snoc44 (snoc44 (snoc44 g a) B) C) a
v244 = var44 (vs44 (vs44 vz44))

v344 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm44 (snoc44 (snoc44 (snoc44 (snoc44 g a) B) C) D) a
v344 = var44 (vs44 (vs44 (vs44 vz44)))

v444 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm44 (snoc44 (snoc44 (snoc44 (snoc44 (snoc44 g a) B) C) D) E) a
v444 = var44 (vs44 (vs44 (vs44 (vs44 vz44))))

test44 : {g:_}-> {a:_} -> Tm44 g (arr44 (arr44 a a) (arr44 a a))
test44  = lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044)))))))
