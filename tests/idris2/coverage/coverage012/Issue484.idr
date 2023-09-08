%default covering

data Three = Vrai | Faux | Indef

getType : Three -> Type
getType Vrai = Unit
getType Faux = Unit
getType Indef = Void

swap : (t : Three) -> getType t -> Three
swap Indef _ impossible
swap Vrai () = Faux
