module Libraries.Text.PrettyPrint.Prettyprinter.Symbols

import Libraries.Text.PrettyPrint.Prettyprinter.Doc

%default total

export
squote : Doc ann
squote = pretty0 '\''

export
dquote : Doc ann
dquote = pretty0 '"'

export
lparen : Doc ann
lparen = pretty0 '('

export
rparen : Doc ann
rparen = pretty0 ')'

export
langle : Doc ann
langle = pretty0 '<'

export
rangle : Doc ann
rangle = pretty0 '>'

export
lbracket : Doc ann
lbracket = pretty0 '['

export
rbracket : Doc ann
rbracket = pretty0 ']'

export
lbrace : Doc ann
lbrace = pretty0 '{'

export
rbrace : Doc ann
rbrace = pretty0 '}'

export
semi : Doc ann
semi = pretty0 ';'

export
colon : Doc ann
colon = pretty0 ':'

export
comma : Doc ann
comma = pretty0 ','

export
space : Doc ann
space = pretty0 ' '

export
dot : Doc ann
dot = pretty0 '.'

export
slash : Doc ann
slash = pretty0 '/'

export
backslash : Doc ann
backslash = pretty0 '\\'

export
equals : Doc ann
equals = pretty0 '='

export
pipe : Doc ann
pipe = pretty0 '|'

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
brackets : {default lbracket ldelim : Doc ann} ->
           {default rbracket rdelim : Doc ann} ->
           Doc ann -> Doc ann
brackets {ldelim, rdelim} = enclose ldelim rdelim

export
braces : Doc ann -> Doc ann
braces = enclose lbrace rbrace
