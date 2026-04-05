module PrettyTerm
  ( module Prettyprinter,
    Prec,
    parensIf,
    lamPrec,
    annPrec,
    sumPrec,
    arrowPrec,
    appPrec,
    atomPrec,
    lambdaSym,
    bigLambdaSym,
    forallSym,
    arrowSym,
    render,
  )
where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

type Prec = Int

lamPrec, annPrec, sumPrec, arrowPrec, appPrec, atomPrec :: Prec
lamPrec = 0
annPrec = 1
sumPrec = 2
arrowPrec = 3
appPrec = 4
atomPrec = 5

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True d = "(" <> d <> ")"
parensIf False d = d

lambdaSym, bigLambdaSym, forallSym, arrowSym :: Doc ann
lambdaSym = "λ"
bigLambdaSym = "Λ"
forallSym = "∀"
arrowSym = "→"

render :: Doc ann -> String
render = renderString . layoutPretty defaultLayoutOptions
