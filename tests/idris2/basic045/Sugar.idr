%default total

zero : Int -> String #0-> (n : Int) -> ()

one : Int #1-> (0 _ : String) -> ()

multiple : Int #1-> Int #0-> Nat -> ()

equality : 2 = 3 #0-> Void

fail1 : String #3-> ()

fail2 : String # 3-> ()

fail3 : String #3 -> ()

fail4 : String #-> ()
