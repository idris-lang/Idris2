
import Data.List

maybeAdd : Maybe Int -> Int -> Int
maybeAdd x y = maybe id (+) x y
