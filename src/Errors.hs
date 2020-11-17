module Errors (unsupported, panic) where

genericUnsupportedMsg :: String
specificUnsupportedMsg :: String -> String
(genericUnsupportedMsg, specificUnsupportedMsg) =
  (prefix ++ " (perhaps a syntax error?)", \reason -> prefix ++ ": " ++ reason)
  where
    prefix = "CodeProperty encountered something it doesn't support"

unsupported :: String -> a
unsupported = error . specificUnsupportedMsg

panic :: a
panic = error genericUnsupportedMsg