data Bad = MkBad (Not Bad)

hmmm : Bad -> Not Bad
hmmm (MkBad n) = n

ok : Not Bad
ok bad = hmmm bad bad

bad : Bad
bad = MkBad ok

total
ohno : Void
ohno = ok bad
