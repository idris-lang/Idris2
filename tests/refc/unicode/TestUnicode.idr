module TestUnicode

import Data.String
import Data.String.Iterator

main : IO ()
main = do
  -- 2-byte UTF-8: h é l l o  (é = U+00E9)
  let umlaut = "héllo"
  putStrLn $ show (length umlaut)                              -- 5
  putStrLn $ show (assert_total $ strIndex umlaut 0)           -- 'h'
  putStrLn $ assert_total (strTail umlaut)                     -- "éllo"
  putStrLn $ show (assert_total $ strIndex umlaut 1)           -- 'é'
  putStrLn $ reverse umlaut                                    -- "olléh"
  putStrLn $ substr 1 2 umlaut                                 -- "él"

  -- 3-byte UTF-8: 世 (U+4E16) 界 (U+754C)
  let cjk = "世界"
  putStrLn $ show (length cjk)                                 -- 2
  putStrLn $ show (assert_total $ strIndex cjk 0)              -- '世'
  putStrLn $ assert_total (strTail cjk)                        -- "界"
  putStrLn $ show (assert_total $ strIndex cjk 1)              -- '界'
  putStrLn $ reverse cjk                                       -- "界世"
  putStrLn $ substr 0 1 cjk                                    -- "世"
  putStrLn $ substr 1 1 cjk                                    -- "界"

  -- 4-byte UTF-8: 😀 (U+1F600)
  let emoji = "hi😀"
  putStrLn $ show (length emoji)                               -- 3
  putStrLn $ show (assert_total $ strIndex emoji 2)            -- '😀'
  putStrLn $ assert_total (strTail emoji)                      -- "i😀"

  -- strCons with a non-ASCII char
  let cons1 = strCons '世' "界"
  putStrLn cons1                                               -- "世界"
  putStrLn $ show (length cons1)                               -- 2

  -- fastPack / fastUnpack round-trip
  let packed = fastPack ['世', '界']
  putStrLn packed                                              -- "世界"
  putStrLn $ show (fastUnpack "世界")                         -- ['世','界']

  -- StringIterator on multi-byte content
  putStrLn $ show (Data.String.Iterator.unpack "世界")        -- ['世','界']

  -- ord / chr round-trip
  putStrLn $ show (ord 'é')                                    -- 233
  putStrLn $ show (chr 233)                                    -- 'é'
  putStrLn $ show (ord '😀')                                  -- 128512
  putStrLn $ show (chr 128512)                                 -- '😀'
