-- | The debugger's views as terminal text, for clients such as hevm-debug
module EVM.Debugger.Text (renderView, valueText) where

import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as BS16
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Hexdump (prettyHex)
import Numeric (showHex)
import Text.Read (readMaybe)

import EVM.Debugger

renderView :: View -> Text
renderView v = T.unlines $
  [ "== step " <> tshow v.step <> " | " <> v.mode <> " | " <> v.status
    <> " | pc " <> hex v.pc <> " " <> v.op <> " | depth " <> tshow v.depth
    <> maybe "" (\g -> " | gas " <> tshow g) v.gas
    <> (if v.branchMode == "solver" then "" else " | branches " <> v.branchMode)
    <> (if v.simplified then "" else " | not simplified")
    <> (if v.merging then " | merging" else "")
  , "contract " <> v.contract <> (if v.codeContract /= v.contract then " (code of " <> v.codeContract <> ")" else "")
  , ""
  , "-- code" <> maybe "" (" of " <>) v.codeName
  ] <> [ (if c.current then " > " else "   ") <> hex c.pc <> "  " <> c.op <> maybe "" (\a -> " " <> valueText (HexValue a)) c.arg | c <- v.code ]
  <> [ "", "-- stack (top first)" ]
  <> (if null v.stack then ["   <empty>"] else [ "   " <> tshow i <> ": " <> valueText e | (i, e) <- zip [0 :: Int ..] v.stack ])
  <> maybe [] (\sv -> ["", "-- source " <> sv.file <> ":" <> tshow sv.line]
                      <> [ (if l.current then " > " else "   ") <> T.justifyRight 5 ' ' (tshow l.line) <> " | " <> l.text | l <- sv.lines, abs (l.line - sv.line) <= 4 ]) v.source
  <> [ "\n-- no source: compiler-generated code, such as ABI decoding or overflow checks" | v.generatedCode ]
  <> [ "", "-- memory (" <> tshow v.memorySize <> " bytes)" ]
  <> (if v.memorySize == 0 then [] else memoryLines v.memory)
  <> concat [ ["", "-- storage of " <> (case st.address of { HexValue h -> h; ExprValue e -> e }) <> " (initial storage " <> st.initial <> ")"]
              <> [ "   " <> valueText sl.slot <> " = " <> valueText sl.value | sl <- st.slots ]
            | st <- v.storage, st.current, not (null st.slots) ]
  <> [ "\npath conditions: " <> tshow v.pathConditions <> " (see 'pathconds')" | v.pathConditions > 0 ]
  <> [ "branches taken: " <> T.intercalate ", " v.choices | not (null v.choices) ]
  <> [ "breakpoints: " <> T.intercalate ", " [ tshow i <> ": " <> b | (i, b) <- zip [0 :: Int ..] v.breakpoints ] | not (null v.breakpoints) ]
  <> maybe [] (\b -> [ "", "-- symbolic branch pending" ]
                     <> maybe [] (\c -> ["   condition: " <> c]) b.condition
                     <> [ "   options: " <> T.intercalate " | " [ tshow i <> ": " <> o | (i, o) <- zip [0 :: Int ..] b.options ] ]) v.branch
  <> (if null v.warnings then [] else ["", "-- warnings"] <> map ("   " <>) v.warnings)
  <> maybe [] (\r -> ["", "result: " <> resultText r]) v.result
  <> maybe [] (\o -> ["", o]) v.output
  <> [ "\n" <> v.message | not (T.null v.message) ]

-- | A value as text, small words also in decimal
valueText :: ValueView -> Text
valueText = \case
  HexValue h -> h <> case readMaybe (T.unpack h) :: Maybe Integer of
    Just w | w < 0x10000 && w > 9 -> " (" <> tshow w <> ")"
    _ -> ""
  ExprValue e -> T.intercalate "\n" (fewLines (T.lines e))

-- | Expressions come whole, which can be thousands of lines
fewLines :: [Text] -> [Text]
fewLines ls
  | length ls <= 20 = ls
  | otherwise = take 20 ls <> ["   … " <> tshow (length ls - 20) <> " more lines"]

memoryLines :: ValueView -> [Text]
memoryLines = \case
  HexValue h | Right bs <- BS16.decodeBase16Untyped (encodeUtf8 (T.drop 2 h)), not (BS.null bs) -> T.lines (T.pack (prettyHex bs))
  m -> T.lines (valueText m)

resultText :: ResultView -> Text
resultText r = r.outcome <> maybe "" (\o -> ", returned " <> output o) r.output <> maybe "" (": " <>) r.problem
  where
    output = \case
      HexValue "0x" -> "nothing"
      o -> valueText o

hex :: Int -> Text
hex n = T.pack ("0x" <> showHex n "")

tshow :: Show a => a -> Text
tshow = T.pack . show
