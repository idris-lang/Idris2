module Main

-- Sample browser-style application for E2E source map testing
-- Tests that --cg javascript source maps work correctly

-- Line 7: DOM-like string manipulation
createElement : String -> String -> String
createElement tag content = "<" ++ tag ++ ">" ++ content ++ "</" ++ tag ++ ">"

-- Line 11: Event handler simulation
handleClick : String -> String
handleClick target = "Clicked: " ++ target

-- Line 15: State update pattern (common in browser apps)
data AppState = MkAppState String Int

updateState : AppState -> String -> AppState
updateState (MkAppState _ count) newMsg = MkAppState newMsg (count + 1)

-- Line 21: Conditional rendering
renderButton : Bool -> String
renderButton True = createElement "button" "Enabled"
renderButton False = createElement "span" "Disabled"

-- Line 26: List rendering (common pattern)
renderList : List String -> String
renderList [] = ""
renderList (x :: xs) = createElement "li" x ++ renderList xs

-- Line 31: Complex nested expression
buildPage : String -> List String -> String
buildPage title items =
  createElement "html" $
    createElement "head" (createElement "title" title) ++
    createElement "body" (
      createElement "h1" title ++
      createElement "ul" (renderList items)
    )

-- Line 40: Main entry point
main : IO ()
main = do
  let page = buildPage "Test Page" ["Item 1", "Item 2", "Item 3"]
  putStrLn page
  let state = MkAppState "initial" 0
  let state' = updateState state "updated"
  case state' of
    MkAppState msg count => putStrLn $ "State: " ++ msg ++ " (" ++ show count ++ ")"
  putStrLn $ handleClick "button#submit"
  putStrLn $ renderButton True
