%default total

nonproductive : Stream a -> (Stream a, ())
nonproductive (x :: xs) =
  case nonproductive xs of
    (xs, ()) => (xs, ())
