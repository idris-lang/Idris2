module Idris.CommandLine.HelpTopic

import Core.Options.Log     -- loggingHelpMessage
import Idris.Syntax.Pragmas -- pragmaHelpMessage
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

%default total

||| Help topics
public export
record HelpTopic where
  constructor MkHelpTopic
  ||| Used to match topic in `--help [topic name]`
  name        : String
  ||| Printed with `--help topics`
  description : String
  ||| Content to print
  content     : Inf String

mutual
   allHelpTopics : List HelpTopic
   allHelpTopics = [
      (MkHelpTopic "logging" "Show logging topics/levels" loggingHelpMessage),
      (MkHelpTopic "pragma"  "Show all pragmas"           pragmaHelpMessage),
      (MkHelpTopic "topics"  "Show list of topics"        listOfTopicsHelpMessage)
   ]

   listOfTopicsHelpMessage : String
   listOfTopicsHelpMessage = show $ vcat $ map helpTopic allHelpTopics
      where
      helpTopic : HelpTopic -> Doc Void
      helpTopic topic
         = let title = "+" <++> pretty topic.name
               blurb = ((::[]) . indent 2 . reflow) topic.description
            in vcat (title :: blurb)

invalidTopic : String -> HelpTopic
invalidTopic name = MkHelpTopic name "" ("Invalid topic: \{name}.\n" ++ "Use '--help topics' to see all topics you can specify.")

export
recogniseHelpTopic : String -> HelpTopic
recogniseHelpTopic topic_name = do
   let Nothing = find (\topic => topic.name == topic_name) allHelpTopics
   | Just topic => topic
   invalidTopic topic_name
