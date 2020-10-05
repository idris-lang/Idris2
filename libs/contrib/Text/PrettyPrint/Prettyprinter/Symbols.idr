module Text.PrettyPrint.Prettyprinter.Symbols

import Text.PrettyPrint.Prettyprinter.Doc

%default total

export
squote : Doc ann
squote = pretty '\''

export
dquote : Doc ann
dquote = pretty '"'

export
lparen : Doc ann
lparen = pretty '('

export
rparen : Doc ann
rparen = pretty ')'

export
langle : Doc ann
langle = pretty '<'

export
rangle : Doc ann
rangle = pretty '>'

export
lbracket : Doc ann
lbracket = pretty '['

export
rbracket : Doc ann
rbracket = pretty ']'

export
lbrace : Doc ann
lbrace = pretty '{'

export
rbrace : Doc ann
rbrace = pretty '}'

export
semi : Doc ann
semi = pretty ';'

export
colon : Doc ann
colon = pretty ':'

export
comma : Doc ann
comma = pretty ','

export
space : Doc ann
space = pretty ' '

export
dot : Doc ann
dot = pretty '.'

export
slash : Doc ann
slash = pretty '/'

export
backslash : Doc ann
backslash = pretty '\\'

export
equals : Doc ann
equals = pretty '='

export
pipe : Doc ann
pipe = pretty '|'

export
squotes : Doc ann -> Doc ann
squotes = enclose squote squote

export
dquotes : Doc ann -> Doc ann
dquotes = enclose dquote dquote

export
parens : Doc ann -> Doc ann
parens = enclose lparen rparen

export
parenthesise : Bool -> Doc ann -> Doc ann
parenthesise b = if b then parens else id

export
angles : Doc ann -> Doc ann
angles = enclose langle rangle

export
brackets : Doc ann -> Doc ann
brackets = enclose lbracket rbracket

export
braces : Doc ann -> Doc ann
braces = enclose lbrace rbrace
