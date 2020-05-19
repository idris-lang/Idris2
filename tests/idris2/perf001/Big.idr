import Data.Vect

test : Vect 33 Int -> IO Int
test bytes_list = do
  let int1 = (index 0 bytes_list * 8) +
             (index 1 bytes_list * 4) +
             (index 2 bytes_list * 2) + (index 3 bytes_list)
  let int2 = (index 4 bytes_list * 8) + (index 5 bytes_list * 4) + (index 6 bytes_list * 2) + (index 7 bytes_list)
  let int3 = (index 8 bytes_list * 8) + (index 9 bytes_list * 4) + (index 10 bytes_list * 2) + (index 11 bytes_list)
  let int4 = (index 12 bytes_list * 8) + (index 13 bytes_list * 4) + (index 14 bytes_list * 2) + (index 15 bytes_list)
  let int5 = (index 12 bytes_list * 8) + (index 13 bytes_list * 4) + (index 14 bytes_list * 2) + (index 15 bytes_list)
  let int6 = (index 12 bytes_list * 8) + (index 13 bytes_list * 4) + (index 14 bytes_list * 2) + (index 15 bytes_list)
  let int7 = (index 12 bytes_list * 8) + (index 13 bytes_list * 4) + (index 14 bytes_list * 2) + (index 15 bytes_list)
  let int8 = (index 12 bytes_list * 8) + (index 13 bytes_list * 4) + (index 14 bytes_list * 2) + (index 15 bytes_list)
  let int9 = (index 12 bytes_list * 8) + (index 13 bytes_list * 4) + (index 14 bytes_list * 2) + (index 15 bytes_list)
  let int10 = (index 12 bytes_list * 8) + (index 13 bytes_list * 4) + (index 14 bytes_list * 2) + (index 15 bytes_list)
  pure int1

