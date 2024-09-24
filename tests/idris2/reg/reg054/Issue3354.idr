import Data.Fin

covering
g : Fin 64 -> Unit
g FZ      = ()
g (FS i') = g $ weaken i'


total
g' : Fin 64 -> Unit
g' FZ        = ()
g' i@(FS i') = g' $ assert_smaller i $ weaken i'
