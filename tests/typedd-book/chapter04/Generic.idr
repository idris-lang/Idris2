safeDivide : Double -> Double -> Maybe Double
safeDivide x y = if y == 0 then Nothing
                           else Just (x / y)
