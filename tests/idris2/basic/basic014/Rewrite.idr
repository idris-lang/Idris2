plusnZ : (n : Nat) -> n + 0 = n
plusnZ 0 = Refl
plusnZ (S k) = rewrite plusnZ k in Refl

plusnSm : (n, m : Nat) -> n + (S m) = S (n + m)
plusnSm Z m = Refl
plusnSm (S k) m = rewrite plusnSm k m in Refl

plusCommutes : (n, m : Nat) -> n + m = m + n
plusCommutes Z m = sym (plusnZ m)
plusCommutes (S k) m = rewrite plusCommutes k m in sym (plusnSm m k)

wrongCommutes : (n, m : Nat) -> n + m = m + n
wrongCommutes Z m = sym (plusnZ m)
wrongCommutes (S k) m = rewrite plusCommutes m k in ?bar

wrongCommutes2 : (n, m : Nat) -> n + m = m + n
wrongCommutes2 Z m = sym (plusnZ m)
wrongCommutes2 (S k) m = rewrite m in ?bar
