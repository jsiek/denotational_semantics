module Delay where

open import Data.List using (List; []; _∷_; _++_; length; replicate)

open import ISWIMAnnot
open import ClosLang
open import Sig

delay : ISWIMAnn → Clos
delay-arg : ∀{b} → Arg b → Argᵪ b

delay (` x) = % x
delay (ƛ fs bN) = 〔 (κ length fs , delay-arg bN) , capture fs 〕
delay (L · M) = (((delay L) ❲ 0 ❳) ▪ ((delay L) ❲ 1 ❳)) ▫ delay M
delay ($ p k) = # p k

delay-arg {■} (ast M) = astᵪ (delay M)
delay-arg {ν b} (bind arg) = bindᵪ (delay-arg {b} arg)
delay-arg {∁ b} (clear arg) = clearᵪ (delay-arg {b} arg)


