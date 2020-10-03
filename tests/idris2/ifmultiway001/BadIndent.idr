-- Check that we're appropriatly parsing as a block
badIndent : Int -> Char
badIndent i = if | i + 3       == 7  => '7'
            | i      == 0
             => '0'
            | i < 0 =>
        'N'
            | _ => 'X'
