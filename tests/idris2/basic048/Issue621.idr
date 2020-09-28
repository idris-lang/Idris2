module Issue621

%default total

a1 : Char
a1 = 'a'

a2 : Char
a2 = 'a'

whyNot : a1 = a2
whyNot = Refl
