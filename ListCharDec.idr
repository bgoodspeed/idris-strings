
module ListCharDec

import CharDec
import ListQuantifiers


%default total

allUpperDec : (cs : List Char) -> Dec (All isUpperT cs)
allUpperDec cs = all isUpperDec cs

anyUpperDec : (cs : List Char) -> Dec (Any isUpperT cs)
anyUpperDec cs = any isUpperDec cs

allLowerDec : (cs : List Char) -> Dec (All isLowerT cs)
allLowerDec cs = all isLowerDec cs

anyLowerDec : (cs : List Char) -> Dec (Any isLowerT cs)
anyLowerDec cs = any isLowerDec cs

allAlphaDec : (cs : List Char) -> Dec (All isAlphaT cs)
allAlphaDec cs = all isAlphaDec cs

anyAlphaDec : (cs : List Char) -> Dec (Any isAlphaT cs)
anyAlphaDec cs = any isAlphaDec cs


allDigitDec : (cs : List Char) -> Dec (All isDigitT cs)
allDigitDec cs = all isDigitDec cs

anyDigitDec : (cs : List Char) -> Dec (Any isDigitT cs)
anyDigitDec cs = any isDigitDec cs

allAlphaNumDec : (cs : List Char) -> Dec (All isAlphaNumT cs)
allAlphaNumDec cs = all isAlphaNumDec cs

anyAlphaNumDec : (cs : List Char) -> Dec (Any isAlphaNumT cs)
anyAlphaNumDec cs = any isAlphaNumDec cs


allNLDec : (cs : List Char) -> Dec (All isNLT cs)
allNLDec cs = all isNLDec cs

anyNLDec : (cs : List Char) -> Dec (Any isNLT cs)
anyNLDec cs = any isNLDec cs



allHexDigitDec : (cs : List Char) -> Dec (All isHexDigitT cs)
allHexDigitDec cs = all isHexDigitDec cs

anyHexDigitDec : (cs : List Char) -> Dec (Any isHexDigitT cs)
anyHexDigitDec cs = any isHexDigitDec cs

allOctDigitDec : (cs : List Char) -> Dec (All isOctDigitT cs)
allOctDigitDec cs = all isOctDigitDec cs

anyOctDigitDec : (cs : List Char) -> Dec (Any isOctDigitT cs)
anyOctDigitDec cs = any isOctDigitDec cs


allSpaceDec : (cs : List Char) -> Dec (All isSpaceT cs)
allSpaceDec cs = all isSpaceDec cs 

anySpaceDec : (cs : List Char) -> Dec (Any isSpaceT cs)
anySpaceDec cs = any isSpaceDec cs 


