import Data.UUID

main : IO ()
main = do
  printLn $ show nil
  printLn $ show $ MkUUID 8329742 6528743
  let uuid = Data.UUID.fromHexa "de318a4f-7fdf-2fb4-48d9-b96ccf20a1eb"
  printLn $ map timeBits uuid
  printLn $ map clockNodeBits uuid
