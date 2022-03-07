import Data.String
import Data.List1

%default total

singletonReduces : singleton 'x' = "x"
singletonReduces = Refl

replicateReduces : replicate 10 'x' = "xxxxxxxxxx"
replicateReduces = Refl

indentReduces : indent 10 "Lorem ipsum" = "          Lorem ipsum"
indentReduces = Refl

padLeftReduces : padLeft 20 ' ' "Lorem ipsum" = "         Lorem ipsum"
padLeftReduces = Refl

padRightReduces : padRight 20 ' ' "Lorem ipsum" = "Lorem ipsum         "
padRightReduces = Refl

wordsReduces : words "Lorem ipsum  dolor   sit    amet" = ["Lorem", "ipsum", "dolor", "sit", "amet"]
wordsReduces = Refl

unwordsReduces : unwords ["Lorem", "ipsum", "dolor", "sit", "amet"] = "Lorem ipsum dolor sit amet"
unwordsReduces = Refl

linesReduces : lines "\rA BC\nD\r\nE\n" = ["", "A BC", "D", "E"]
linesReduces = Refl

unlinesReduces : unlines ["line", "line2", "ln3", "D"] = "line\nline2\nln3\nD\n"
unlinesReduces = Refl

strMReduces : strM "abc" = StrCons 'a' "bc"
strMReduces = Refl

asListReduces : asList "abc" = ['a', 'b', 'c']
asListReduces = Refl

ltrimReduces : ltrim " Lorem ipsum" = "Lorem ipsum"
ltrimReduces = Refl

trimReduces : trim " Lorem ipsum " = "Lorem ipsum"
trimReduces = Refl

spanReduces : span (/= 'C') "ABCD" = ("AB", "CD")
spanReduces = Refl

breakReduces : break (== 'C') "ABCD" = ("AB", "CD")
breakReduces = Refl

splitReduces : split (== '.') ".AB.C..D" = "" ::: ["AB", "C", "", "D"]
splitReduces = Refl

stringToNatOrZReduces : stringToNatOrZ "0" = 0
stringToNatOrZReduces = Refl

toUpperReduces : toUpper "abc" = "ABC"
toUpperReduces = Refl

toLowerReduces : toLower "ABC" = "abc"
toLowerReduces = Refl

strIndexReduces : strIndex "abc" 0 = 'a'
strIndexReduces = Refl

strLengthReduces : strLength "abc" = 3
strLengthReduces = Refl

strSubstrReduces : strSubstr 0 1 "abc" = "a"
strSubstrReduces = Refl

strTailReduces : strTail "abc" = "bc"
strTailReduces = Refl

isPrefixOfReduces : isPrefixOf "ab" "abc" = True
isPrefixOfReduces = Refl

isSuffixOfReduces : isSuffixOf "bc" "abc" = True
isSuffixOfReduces = Refl

isInfixOfReduces : isInfixOf "b" "abc" = True
isInfixOfReduces = Refl

nullReduces : null "" = True
nullReduces = Refl
